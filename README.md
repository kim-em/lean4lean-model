# lean4lean-model

A Lean 4 package for model constructions over the [lean4lean](https://github.com/digama0/lean4lean)
formalization of Lean's type theory, with [mathlib](https://github.com/leanprover-community/mathlib4)
available for the mathematical side.

## Building

```sh
lake exe cache get   # mathlib oleans
lake build
```

Everything is pinned at Lean `v4.32.2`: mathlib `v4.32.2`, lean4lean `master`.

Note that importing lean4lean alongside mathlib requires lean4lean's stdlib prelude
(`Lean4Lean/Std/Basic.lean`) to live in the `Lean4Lean` namespace rather than the root one --
12 of its names are also mathlib names, and the environment merge rejects duplicate constants.
That is the case on lean4lean master as of `7842f38`; consumers just need an `open Lean4Lean`.

## Target

`Lean4LeanModel/Consistency.lean` states the goal: consistency of the type theory formalized in
`Lean4Lean.Theory`, assuming `ω` inaccessible cardinals -- the soundness theorem of *The Type
Theory of Lean*. It is `sorry`ed pending the model construction.
