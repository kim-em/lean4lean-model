# lean4lean-model

A Lean 4 package for model constructions over the [lean4lean](https://github.com/digama0/lean4lean)
formalization of Lean's type theory, with [mathlib](https://github.com/leanprover-community/mathlib4)
available for the mathematical side.

## Building

```sh
lake exe cache get   # mathlib oleans
lake build
```

Everything is pinned at Lean `v4.30.0`: mathlib `v4.30.0`, lean4lean `7842f38`.

Note that importing lean4lean alongside mathlib requires lean4lean's stdlib prelude
(`Lean4Lean/Std/Basic.lean`) to live in the `Lean4Lean` namespace rather than the root one --
12 of its names are also mathlib names, and the environment merge rejects duplicate constants.
That is the case on lean4lean master as of `7842f38`; consumers just need an `open Lean4Lean`.

## Target

`Lean4LeanModel/Consistency.lean` states the goal: consistency of the type theory formalized in
`Lean4Lean.Theory`, assuming `ω` inaccessible cardinals and restricting initially to a standard
declaration fragment. The fragment admits ordinary definitions, the canonical `Eq`, `Iff`, and
`Nonempty` inductives, primitive quotients, and exactly Lean's three standard axioms (`propext`,
`Classical.choice`, and `Quot.sound`). Standard names are reserved and each axiom checks that its
canonical dependencies are already present, so a same-typed replacement cannot silently change
their meanings. This is the first model theorem toward the soundness theorem of *The Type Theory
of Lean*. It is `sorry`ed pending the model construction.

General inductive declarations remain out of scope because the upstream `VInductDecl.WF` and
`VEnv.addInduct` specifications are still `sorry`. The standard inductives are fixed explicitly so
their set-theoretic models can be handled as dedicated cases without first modeling all inductives.
