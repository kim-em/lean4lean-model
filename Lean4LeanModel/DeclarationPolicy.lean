import Lean4Lean.Theory.Typing.Env

/-!
# Declaration policies

The abstract `Lean4Lean.VEnv.WF` predicate permits arbitrary well-typed axioms, and its inductive
declaration case is not yet specified. Soundness milestones therefore need an additional policy
saying which declarations may occur in the history of an environment.
-/

namespace Lean4LeanModel

open Lean4Lean

/-- A well-formed environment with a declaration history accepted by `allowed`. -/
def WFUnder (allowed : VDecl → Prop) (env : VEnv) : Prop :=
  ∃ ds, VEnv.WF' ds env ∧ ∀ d ∈ ds, allowed d

/-- Forgetting the declaration policy leaves an ordinary well-formed environment. -/
theorem WFUnder.wf {allowed : VDecl → Prop} {env : VEnv} :
    WFUnder allowed env → VEnv.WF env
  | ⟨ds, hds, _⟩ => ⟨ds, hds⟩

/-- Extend a policy-compliant history by one policy-compliant declaration. -/
theorem WFUnder.decl {allowed : VDecl → Prop} {env env' : VEnv} {d : VDecl}
    (h : WFUnder allowed env) (hd : VDecl.WF env d env') (ha : allowed d) :
    WFUnder allowed env' := by
  obtain ⟨ds, hds, hall⟩ := h
  refine ⟨d :: ds, .decl hd hds, ?_⟩
  intro d' hd'
  simp only [List.mem_cons] at hd'
  rcases hd' with rfl | hd'
  · exact ha
  · exact hall d' hd'

/-- Weakening a declaration policy preserves well-formedness under that policy. -/
theorem WFUnder.mono {allowed allowed' : VDecl → Prop} {env : VEnv}
    (h : WFUnder allowed env) (hle : ∀ d, allowed d → allowed' d) :
    WFUnder allowed' env := by
  obtain ⟨ds, hds, hall⟩ := h
  exact ⟨ds, hds, fun d hd => hle d (hall d hd)⟩

/-- The declarations supported by the first model milestone. The exhaustive match is deliberate:
new declaration forms upstream must be reviewed before entering the modeled fragment. Quotient
declarations are included, but the `Quot.sound` axiom is not. -/
def CoreDecl : VDecl → Prop
  | .block _ => True
  | .axiom _ => False
  | .def _ => True
  | .opaque _ => True
  | .example _ => True
  | .quot => True
  | .induct _ => False

/-- A well-formed environment in the axiom-free, inductive-free core fragment. -/
abbrev CoreWF (env : VEnv) : Prop := WFUnder CoreDecl env

theorem core_empty : CoreWF .empty := by
  exact ⟨[], .empty, by simp⟩

end Lean4LeanModel
