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
`Lean4Lean.Theory`, assuming `ω` inaccessible cardinals and initially restricting to declaration
histories without axioms or inductive declarations. Primitive quotient declarations remain in
scope. This is the first model theorem toward the soundness theorem of *The Type Theory of Lean*.
It is `sorry`ed pending the model construction.

Allowing Lean's standard axioms (`propext`, `Classical.choice`, and `Quot.sound`) additionally
requires pinning the standard meanings of dependencies such as `Eq`, `Iff`, and `Nonempty`.
Those are inductive declarations, whose abstract specification is still unfinished in lean4lean.
General inductive declarations are excluded from the initial target because the upstream
`VInductDecl.WF` and `VEnv.addInduct` specifications are still `sorry` and provide no information
with which to construct their model.
