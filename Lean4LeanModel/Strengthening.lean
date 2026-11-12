import Lean4LeanModel.KlopSetModel
import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Statement

/-!
# Strengthening of definitional equality fails

`not_weakN_iff`: the statement of `Lean4Lean.VEnv.IsDefEqU.weakN_iff` (context strengthening for
definitional equality, in every well-formed environment) is false. The counterexample is Klop's
term in an environment with canonical `Eq` and a looping definition; its two sides are separated
by a model built in `ZFSet`, with no hypothesis on cardinals.
-/

namespace Lean4LeanModel

open Lean4Lean Lean4Lean.VEnv.Strengthening

/-- **The statement of `IsDefEqU.weakN_iff` is false.** -/
theorem not_weakN_iff :
    ¬ ∀ {env : VEnv} {U n k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr},
      env.WF → OnCtx Γ' (env.IsType U) → Ctx.LiftN n k Γ Γ' →
      (env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) ↔ env.IsDefEqU U Γ e1 e2) :=
  not_weakN_iff_of_setModel zfSetModel.{0}

end Lean4LeanModel
