import Lean4LeanModel.Semantics
import Lean4Lean.Theory.Typing.Env

/-!
# Well-formed environments that prove `False`

`VEnv.WF` admits environments with a closed term of type `VExpr.false` that declare no axiom. The
unrestricted target `Lean4LeanModel.consistency` is therefore refutable for a second reason besides
arbitrary axioms, and so is every statement quantified over histories that restricts only the
axioms (`model_of_wfHistory_withAxioms`): the histories also have to be restricted in their
`mutualDef` steps.

Nothing in the model depends on this module; it records a checked fact about the theory.
-/

namespace Lean4LeanModel

open Lean4Lean

/-- The definition `loop : ∀ (p : Prop), p := loop`. -/
def loopDef : VDefVal where
  uvars := 0
  type := VExpr.false
  name := `loop
  value := .const `loop []

/-- The environment declaring `loop` as a constant. -/
def loopConstEnv : VEnv :=
  { VEnv.empty with
    constants := fun n => if `loop = n then some loopDef.toVConstant else VEnv.empty.constants n }

/-- A `mutualDef` block types its values with the block's constants already declared, so the
one-element block `loop := loop` is well formed over the empty environment. The resulting
environment is well formed, declares no axiom, and has a closed term of type
`∀ (p : Prop), p`. -/
theorem wf_mutualDef_proves_false :
    ∃ env : VEnv, VEnv.WF' [.mutualDef [loopDef]] env ∧
      ∃ e, env.HasType 0 [] e VExpr.false := by
  have hfalse : ∀ env : VEnv, env.HasType 0 [] VExpr.false
      (.sort (.imax (.succ .zero) .zero)) := fun env =>
    .forallEDF (.sortDF (by trivial) (by trivial) rfl) (.bvar .zero)
  have hadd : VEnv.empty.addConsts [loopDef] = some loopConstEnv := rfl
  have hconst : loopConstEnv.HasType 0 [] (.const `loop []) VExpr.false :=
    .constDF (ci := loopDef.toVConstant) (by simp [loopConstEnv]) (by simp) (by simp) rfl .nil
  refine ⟨loopConstEnv.addDefEqs [loopDef], ?_, .const `loop [], ?_⟩
  · refine .decl (.mutualDef ?_ hadd ?_) .empty
    · intro ci hci
      obtain rfl : ci = loopDef := by simpa using hci
      exact ⟨_, hfalse _⟩
    · intro ci hci
      obtain rfl : ci = loopDef := by simpa using hci
      exact hconst
  · exact hconst.mono VEnv.addDefEqs_le

end Lean4LeanModel
