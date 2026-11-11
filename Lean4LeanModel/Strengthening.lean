import Lean4LeanModel.KlopTower
import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Statement

/-!
# Strengthening of definitional equality fails, assuming `ω` inaccessible cardinals

`not_weakN_iff`: the statement of `Lean4Lean.VEnv.IsDefEqU.weakN_iff` (if two terms that do not
mention some binders of a context are definitionally equal in that context, they are
definitionally equal without those binders) is false, assuming `OmegaInaccessibles`. The
counterexample and its model are in lean4lean (`KlopSeparation`); this file supplies the universe
tower the model is built in.
-/

namespace Lean4LeanModel

open Lean4Lean Lean4Lean.VEnv.Strengthening

universe u

/-- **Assuming `ω` inaccessible cardinals, strengthening of definitional equality is false.** -/
theorem not_weakN_iff (h : OmegaInaccessibles.{u}) :
    ¬ ∀ {env : VEnv} {U n k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr},
      env.WF → OnCtx Γ' (env.IsType U) → Ctx.LiftN n k Γ Γ' →
      (env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) ↔ env.IsDefEqU U Γ e1 e2) := by
  obtain ⟨tower⟩ := nonempty_universeTower h
  exact not_weakN_iff_of_tower tower

end Lean4LeanModel

#print axioms Lean4LeanModel.not_weakN_iff
