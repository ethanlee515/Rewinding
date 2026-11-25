# Rewinding

Attempts to port reflection from EasyCrypt to SSProve.

## Build the Rocq project

With the `rewinding` opam switch active and the `rocq-released` repository
enabled, run these commands from this checkout.

```sh
opam pin add . --no-action --working-dir
opam install rewinding --deps-only --working-dir --jobs=4
make clean
make
```

[rewinding.opam](rewinding.opam) pins Mending and SSProve to exact GitHub
commits. Opam downloads and installs them in the switch. Both pins are listed
because opam only processes the `pin-depends` of this checkout. Run `make
clean` before building with a different switch or after changing dependencies.

The default build checks [HelloWorld.v](theories/HelloWorld.v). The coin-toss
starter and other prototypes live in `experiments/`. The research notes
describe what each experiment proves and how to run it.
[Rewinding experiments](notes/rewinding-experiments.md)

### Fresh checkout and switch

Create and select the switch, then add Rocq's package repository.

```sh
opam switch create rewinding 5.4.1
eval "$(opam env --switch=rewinding --set-switch)"
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update --repositories
```

Then install the dependencies and build as above.

## Case studies

TODO

* Coin-toss
* Interactive Schnorr
* Fiat-Shamir for quadratic residuosity
* Blum's Hamiltonian-cycle

## Related works

TODO explain and compare how they deal with this

* VCVio
* CatCrypt
