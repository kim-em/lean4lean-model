import Lean4LeanModel.Context
import Lean4Lean.Theory.Typing.EnvLemmas

/-!
# Global model data

The raw interpreter is total for every assignment, but soundness requires constants, primitive
definitional equations and registered reduction rules to receive values validating their
declarations.  This module records that
global invariant separately from the per-context valuation relation.
-/

namespace Lean4LeanModel

open Lean4Lean

universe u

namespace Assignment

/-- An assignment validates every constant and primitive definitional equation in `env`. -/
structure WF (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u}) : Prop where
  const_mem : ∀ {c ci ns}, env.constants c = some ci → ns.length = ci.uvars →
    assignment.constVal c ns ∈ interp κ env assignment ns [] [] ci.type
  defeq : ∀ {df ns}, env.defeqs df → ns.length = df.uvars →
    interp κ env assignment ns [] [] df.lhs = interp κ env assignment ns [] [] df.rhs

/-- Semantic validity of the registered reduction rules of `env`: the pattern (ι) rules
`env.pats` read by `VEnv.IsDefEq.pat`, and the projection metadata `env.projections` read by
`projDF`, `projIota` and `structEta`.

Each field is the semantic content of one typing rule, stated for an arbitrary instance of the
rule in a modeled context. Its hypotheses are the premises of the rule together with the semantic
facts the fundamental theorem has in hand for those premises (its induction hypotheses), so the
four cases of `fundamentalStrong` are applications of the four fields and nothing else.

This structure is an explicit hypothesis, not a theorem: nothing in this development constructs it
for an environment that has a rule. It is the interface the set-theoretic interpretation of
inductive types has to implement. See `INDUCTIVES_STATUS.md`. -/
structure RulesWF (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u}) : Prop where
  /-- ι reduction (`VEnv.IsDefEq.pat`): a typed instance of a registered pattern rule has the
  same value as its reduct. -/
  pat : ∀ {L : List Nat} {Γ : List VExpr} {γ : List ZFSet.{u}} {p : Pattern}
      {r : p.RHS × p.Check} {e A : VExpr} {m1 m2 chk},
    env.pats p r → p.Matches e m1 m2 →
    OnCtx Γ (env.IsType L.length) → ModelsCtx κ env assignment L Γ γ →
    env.HasType L.length Γ e A →
    env.HasType L.length Γ (r.1.apply m1 m2) A →
    r.2.Realizes m1 m2 chk →
    (∀ t ∈ chk, env.IsDefEq L.length Γ t.1 t.2.1 t.2.2) →
    (∀ t ∈ chk, interp κ env assignment L Γ γ t.1 = interp κ env assignment L Γ γ t.2.1) →
    interp κ env assignment L Γ γ e ∈ interp κ env assignment L Γ γ A →
    interp κ env assignment L Γ γ (r.1.apply m1 m2) ∈ interp κ env assignment L Γ γ A →
    interp κ env assignment L Γ γ e = interp κ env assignment L Γ γ (r.1.apply m1 m2)
  /-- Typing of a primitive projection (`VEnv.IsDefEq.projDF`): the projection of a member of the
  structure is a member of the field type. -/
  proj_mem : ∀ {L : List Nat} {Γ : List VExpr} {γ : List ZFSet.{u}} {typeName : Name}
      {info : VProjectionInfo} {levels : List VLevel} {params indexArgs : List VExpr}
      {index : Nat} {sourceMajor major fieldType : VExpr} {fieldLevel : VLevel},
    env.projections typeName info →
    (∀ l ∈ levels, l.WF L.length) →
    levels.length = info.uvars →
    params.length = info.nparams →
    indexArgs.length = info.nindices →
    info.fieldType typeName levels params index sourceMajor = some fieldType →
    OnCtx Γ (env.IsType L.length) → ModelsCtx κ env assignment L Γ γ →
    env.HasType L.length Γ fieldType (.sort fieldLevel) →
    env.IsDefEq L.length Γ sourceMajor major
      (VExpr.mkApps (.const typeName levels) (params ++ indexArgs)) →
    info.ctorType.Closed →
    ((info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero) →
    interp κ env assignment L Γ γ fieldType ∈ interp κ env assignment L Γ γ (.sort fieldLevel) →
    interp κ env assignment L Γ γ sourceMajor = interp κ env assignment L Γ γ major →
    interp κ env assignment L Γ γ sourceMajor ∈
      interp κ env assignment L Γ γ
        (VExpr.mkApps (.const typeName levels) (params ++ indexArgs)) →
    interp κ env assignment L Γ γ (.proj typeName index major) ∈
      interp κ env assignment L Γ γ fieldType
  /-- Projection of a constructor application (`VEnv.IsDefEq.projIota`). -/
  projIota : ∀ {L : List Nat} {Γ : List VExpr} {γ : List ZFSet.{u}} {typeName : Name}
      {info : VProjectionInfo} {levels : List VLevel} {args : List VExpr} {index : Nat}
      {field fieldType : VExpr},
    env.projections typeName info →
    OnCtx Γ (env.IsType L.length) → ModelsCtx κ env assignment L Γ γ →
    env.HasType L.length Γ
      (.proj typeName index (VExpr.mkApps (.const info.ctorName levels) args)) fieldType →
    args[info.nparams + index]? = some field →
    env.HasType L.length Γ field fieldType →
    interp κ env assignment L Γ γ
        (.proj typeName index (VExpr.mkApps (.const info.ctorName levels) args)) ∈
      interp κ env assignment L Γ γ fieldType →
    interp κ env assignment L Γ γ field ∈ interp κ env assignment L Γ γ fieldType →
    interp κ env assignment L Γ γ
        (.proj typeName index (VExpr.mkApps (.const info.ctorName levels) args)) =
      interp κ env assignment L Γ γ field
  /-- Structure eta (`VEnv.IsDefEq.structEta`). -/
  structEta : ∀ {L : List Nat} {Γ : List VExpr} {γ : List ZFSet.{u}} {typeName : Name}
      {info : VProjectionInfo} {levels : List VLevel} {params : List VExpr} {e : VExpr},
    env.projections typeName info →
    params.length = info.nparams →
    info.nindices = 0 →
    OnCtx Γ (env.IsType L.length) → ModelsCtx κ env assignment L Γ γ →
    env.HasType L.length Γ e (VExpr.mkApps (.const typeName levels) params) →
    env.HasType L.length Γ
      (VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index => .proj typeName index e))
      (VExpr.mkApps (.const typeName levels) params) →
    interp κ env assignment L Γ γ e ∈
      interp κ env assignment L Γ γ (VExpr.mkApps (.const typeName levels) params) →
    interp κ env assignment L Γ γ
        (VExpr.mkApps (.const info.ctorName levels)
          (params ++ (List.range info.numFields).map fun index => .proj typeName index e)) ∈
      interp κ env assignment L Γ γ (VExpr.mkApps (.const typeName levels) params) →
    interp κ env assignment L Γ γ
        (VExpr.mkApps (.const info.ctorName levels)
          (params ++ (List.range info.numFields).map fun index => .proj typeName index e)) =
      interp κ env assignment L Γ γ e

/-- An environment with no pattern rules and no projection metadata has nothing to validate. -/
theorem RulesWF.of_no_rules {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    (hpats : ∀ p r, ¬env.pats p r) (hprojs : ∀ n info, ¬env.projections n info) :
    assignment.RulesWF κ env where
  pat h := (hpats _ _ h).elim
  proj_mem h := (hprojs _ _ h).elim
  projIota h := (hprojs _ _ h).elim
  structEta h := (hprojs _ _ h).elim

/-- `assignment'` preserves the meanings of every constant already present in `env`, and of
the projections of every structure already registered in `env`. -/
structure Extends (env : VEnv) (assignment assignment' : Assignment.{u}) : Prop where
  const : ∀ {c ci}, env.constants c = some ci → ∀ ns,
    assignment'.constVal c ns = assignment.constVal c ns
  proj : ∀ {typeName info}, env.projections typeName info → ∀ index x,
    assignment'.projVal typeName index x = assignment.projVal typeName index x

theorem Extends.rfl (env : VEnv) (assignment : Assignment.{u}) :
    Extends env assignment assignment :=
  ⟨fun _ _ => _root_.rfl, fun _ _ _ => _root_.rfl⟩

end Assignment

/-- Global hypotheses shared by every semantic soundness statement. -/
structure ModelSetup (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u}) : Prop where
  cardinals_strictMono : StrictMono κ
  cardinals_inaccessible : ∀ n, (κ n).IsInaccessible
  environmentWF : env.WF
  assignmentWF : assignment.WF κ env
  /-- The registered ι and projection rules are semantically valid (`Assignment.RulesWF`). -/
  rulesWF : assignment.RulesWF κ env

namespace ModelSetup

theorem envWF {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    (h : ModelSetup κ env assignment) : env.WF :=
  h.environmentWF

theorem envOrdered {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    (h : ModelSetup κ env assignment) : env.Ordered :=
  h.environmentWF.ordered

end ModelSetup

end Lean4LeanModel
