From Stdlib Require Import Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq choice.
From extructures Require Import ord fmap.
From SSProve.Crypt Require Import Package.

Import PackageNotation.
Local Open Scope package_scope.

Definition heap_type : choice_type := chMap chNat chNat.

(** An uninitialized cell represents the empty private heap. *)
Definition heap_location (address : nat) : Location :=
  @mkloc address heap_type empty_heap.

Definition get_state (address : nat) : raw_code (Value heap_type) :=
  getr (heap_location address) (fun h => ret h).

Definition set_state (address : nat) (h : heap) : raw_code (Value chUnit) :=
  putr (heap_location address) h (ret tt).

Fixpoint run_with_heap (address : nat) {A : choiceType} (c : raw_code A) :
    raw_code A :=
  match c with
  | ret x => ret x
  | opr o x k => opr o x (fun y => run_with_heap address (k y))
  | getr l k =>
      h ← get_state address ;;
      run_with_heap address (k (get_heap h l))
  | putr l v k =>
      h ← get_state address ;;
      set_state address (set_heap h l v) ;;
      run_with_heap address k
  | sampler op k => sampler op (fun y => run_with_heap address (k y))
  end.

(** Use the first two IDs above all original exports. *)
Definition get_state_op (exports : Interface) : opsig :=
  mkopsig (S (foldr maxn 0 (unzip1 exports))) chUnit heap_type.

Definition set_state_op (exports : Interface) : opsig :=
  mkopsig (S (ide (get_state_op exports))) heap_type chUnit.

Definition heap_exports (exports : Interface) : Interface :=
  unionm (mkfmap [:: get_state_op exports; set_state_op exports]) exports.

Local Definition heap_locations (address : nat) : Locations :=
  mkfmap [:: heap_location address].

Local Lemma heap_location_present address :
  fhas (heap_locations address) (heap_location address).
Proof. exact: fhas_set. Qed.

Local Lemma run_with_heap_valid address (A : choiceType) (c : raw_code A) L I :
  ValidCode L I c -> ValidCode (heap_locations address) I (run_with_heap address c).
Proof.
move=> H.
elim: H => [x|o x k Ho Hk IH|l k Hl Hk IH|l v k Hl Hk IH|op k Hk IH] /=.
- exact: valid_ret.
- by apply: valid_opr.
- apply: valid_getr; first exact: heap_location_present.
  move=> h. exact: (IH (get_heap h l)).
- apply: valid_getr; first exact: heap_location_present.
  move=> h. apply: valid_putr; first exact: heap_location_present.
  exact: IH.
- by apply: valid_sampler.
Qed.

Local Definition compile_method address (method : typed_raw_function) :
    typed_raw_function :=
  match method with
  | (source; target; body) =>
      mkdef source target (fun x => run_with_heap address (body x))
  end.

Local Lemma compiled_methods_valid address I E (p : package I E) :
  ValidPackage (heap_locations address) I E (mapm (compile_method address) (pack p)).
Proof.
have [_ Hbody] := pack_valid p.
split.
- move=> [id [S T]]. rewrite {1}(valid_exports_eq (pack_valid p)).
  rewrite /fhas /= !mapmE.
  case: (pack p id) => [[S' [T' body]]|] /=.
  + split.
    * move=> [= <- <-]. by eexists.
    * move=> [f H]. injection H; intros; by subst.
  + by split => // -[f].
- move=> id F x. rewrite /fhas mapmE.
  case Hp: (pack p id) => [[S [T body]]|] //=.
  move=> [= HF]. subst F. apply: run_with_heap_valid.
  exact: (Hbody _ _ _ Hp).
Qed.

Local Definition state_methods address exports : raw_package :=
  mkfmap [::
    (ide (get_state_op exports), mkdef chUnit heap_type (fun _ => get_state address));
    (ide (set_state_op exports), mkdef heap_type chUnit (set_state address))].

Local Lemma state_methods_valid address I exports :
  ValidPackage (heap_locations address) I
    (mkfmap [:: get_state_op exports; set_state_op exports])
    (state_methods address exports).
Proof.
apply: valid_package_cons.
- apply: valid_package_cons.
  move=> h. apply: valid_putr; first exact: heap_location_present.
  exact: valid_ret.
- move=> []. apply: valid_getr; first exact: heap_location_present.
  move=> h. exact: valid_ret.
Qed.

(** Compile every export to use the same heap cell. Imports stay as calls.
    Link any dependencies whose state belongs in the snapshot before compiling.
    Reserve [address] in the ambient heap for this package. *)
Definition compile_package (address : nat) {I E : Interface} (p : package I E) :
    package I (heap_exports E).
Proof.
refine (mkpackage (heap_locations address)
  (par (state_methods address E) (mapm (compile_method address) (pack p))) _).
have H := @valid_par _ _ _ _ _ _ _ _
  (state_methods_valid address I E) (compiled_methods_valid address I E p)
  Logic.eq_refl Logic.eq_refl.
by rewrite !unionmI in H.
Defined.
