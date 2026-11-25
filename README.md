# Rewinding

Attempts to port reflection from EasyCrypt to SSProve.

## Build the Rocq starter

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

[CoinToss.v](theories/CoinToss.v) defines a checkpoint immediately before the
committer receives the other party's bit. It gives the joint distribution of
the two opening attempts, each starting from the saved heap. The next proof
needs to obtain that heap and trace from the same execution and construct the
binding adversary as an SSProve package.

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
