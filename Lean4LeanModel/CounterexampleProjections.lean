import Lean4LeanModel.Semantics
import Lean4Lean.Theory.Typing.ProjectionRigidity

/-!
# The projection entry of a non-positive structure

Let `T : Type` and `mk : (T → Prop) → T` be constants, and register `T` as a structure with
constructor `mk` (`cxEnv`). Then `projIota` gives `(mk d).1 ≡ d`, and with
`d := fun t => t.1 t → False`, `m := mk d` and `P := d m` this yields `P ≡ (P → False) : Prop`,
so the self-application `(fun h : P => h h) (fun h : P => h h)` is a closed term of type
`VExpr.false` (`cxEnv_proves_false`).

How `cxEnv` can be reached by a well-formed history:

* Not from the two axioms `T` and `mk`. The projection entries of a well-formed environment are
  those of the declarations its history lists as `.induct`
  (`VEnv.WF'.projection_formation`), so a history without such an entry has no projection
  entry (`not_projections_of_no_induct`, `not_wf_cxEnv_of_no_induct`).
* Every well-formed history of `cxEnv` lists a declaration `.induct D` that has the entry of `T`
  and satisfies the source and formation judgments over a well-formed environment below `cxEnv`
  (`wf_cxEnv_formation`).
* The type formers and constructors of a constructor-and-projection prefix are fresh in the
  environment it extends (`projectionStage_sourceNames_fresh`).
* For the declaration `cxDecl false` (`isUnsafe = false`) over the empty environment, the
  source judgment and the installation hold, so the constructor-and-projection prefix exists
  exactly when the formation judgment does (`cxDecl_projectionStage_iff`). Formation asks for
  strict positivity of the field `T → Prop`. That it fails is not proved here.
* For `cxDecl true` (`isUnsafe = true`) formation does not ask for positivity, the prefix
  exists, and `cxEnv` is well formed with history `[.induct (cxDecl true)]`
  (`wf_unsafe_projectionStage_proves_false`). So histories have to exclude unsafe
  declarations.

Nothing in the model depends on this module; it records checked facts about the theory.
-/

namespace Lean4LeanModel

open Lean4Lean

/-- The type former `T`, as an expression. -/
def cxT : VExpr := .const `T []

/-- `T → Prop`. -/
def cxTP : VExpr := .forallE cxT (.sort .zero)

/-- The axiom `T : Type`. -/
def cxTypeVal : VConstVal := { name := `T, uvars := 0, type := .sort (.succ .zero) }

/-- The axiom `mk : (T → Prop) → T`. -/
def cxMkVal : VConstVal := { name := `mk, uvars := 0, type := .forallE cxTP cxT }

/-- The family `T` with its one constructor `mk`. -/
def cxType : VInductiveType :=
  { name := `T, uvars := 0, type := .sort (.succ .zero), numIndices := 0,
    resultLevel := .succ .zero, ctors := [cxMkVal] }

/-- The non-positive structure declaration `T` with constructor `mk : (T → Prop) → T` and no
recursors, with the given `isUnsafe` flag. -/
def cxDecl (isUnsafe : Bool) : VInductDecl where
  uvars := 0
  nparams := 0
  isUnsafe := isUnsafe
  recs := []
  types := [cxType]

/-- The projection metadata registered for `T`. -/
def cxInfo : VProjectionInfo where
  uvars := 0
  nparams := 0
  nindices := 0
  resultLevel := .succ .zero
  ctorName := `mk
  ctorType := .forallE cxTP cxT

/-- The environment with the constant `T : Type`. -/
def cxEnvT : VEnv :=
  { VEnv.empty with
    constants := fun n => if `T = n then some cxTypeVal.toVConstant else VEnv.empty.constants n }

/-- The environment with the constants `T : Type` and `mk : (T → Prop) → T`. -/
def cxEnvCtors : VEnv :=
  { cxEnvT with
    constants := fun n => if `mk = n then some cxMkVal.toVConstant else cxEnvT.constants n }

/-- `cxEnvCtors` with the projection entry of `T`. The entry does not depend on the `isUnsafe`
flag. -/
def cxEnv : VEnv := cxEnvCtors.addProjections (cxDecl false).projectionEntries

/-- `d := fun t : T => t.1 t → False`. -/
def cxD : VExpr :=
  .lam cxT (.forallE (.app (.proj `T 0 (.bvar 0)) (.bvar 0)) VExpr.false)

/-- `m := mk d`. -/
def cxM : VExpr := .app (.const `mk []) cxD

/-- `P := d m`. -/
def cxP : VExpr := .app cxD cxM

/-- `ω := fun h : P => h h`. -/
def cxOmega : VExpr := .lam cxP (.app (.bvar 0) (.bvar 0))

private theorem toProp {env : VEnv} {U : Nat} {Γ : List VExpr} {a b : VExpr} {l : VLevel}
    (hwf : l.WF U) (hl : l ≈ .zero) (h : env.IsDefEq U Γ a b (.sort l)) :
    env.IsDefEq U Γ a b (.sort .zero) :=
  .defeqDF (.sortDF hwf (by trivial) hl) h

private theorem hasType_false (env : VEnv) (Γ : List VExpr) :
    env.HasType 0 Γ VExpr.false (.sort .zero) := by
  have h : env.HasType 0 Γ VExpr.false (.sort (.imax (.succ .zero) .zero)) :=
    .forallEDF (.sortDF (by trivial) (by trivial) rfl) (.bvar .zero)
  exact toProp (by simp [VLevel.WF]) (by simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax]) h

private theorem hasType_T {env : VEnv} (hc : env.constants `T = some cxTypeVal.toVConstant)
    (Γ : List VExpr) : env.HasType 0 Γ cxT (.sort (.succ .zero)) :=
  .constDF (ci := cxTypeVal.toVConstant) hc (by simp) (by simp) rfl .nil

private theorem hasType_TP {env : VEnv} (hc : env.constants `T = some cxTypeVal.toVConstant)
    (Γ : List VExpr) :
    env.HasType 0 Γ cxTP (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .forallEDF (hasType_T hc Γ) (.sortDF (by trivial) (by trivial) rfl)

private theorem constants_T : cxEnv.constants `T = some cxTypeVal.toVConstant := by
  simp [cxEnv, cxEnvCtors, cxEnvT]

private theorem constants_mk : cxEnv.constants `mk = some cxMkVal.toVConstant := by
  simp [cxEnv, cxEnvCtors]

private theorem projections_T : cxEnv.projections `T cxInfo :=
  VEnv.addProjections_iff.2 (.inl ⟨⟨`T, cxInfo⟩, by
    simp [VInductDecl.projectionEntries, cxDecl, cxType, cxInfo, cxMkVal], rfl, rfl⟩)

/-- The first projection of any `major : T` has type `T → Prop`. -/
private theorem hasType_proj {Γ : List VExpr} {major : VExpr}
    (hm : cxEnv.HasType 0 Γ major cxT) : cxEnv.HasType 0 Γ (.proj `T 0 major) cxTP :=
  .projDF (info := cxInfo) (levels := []) (params := []) (indexArgs := [])
    (sourceMajor := major) projections_T (by simp) rfl rfl rfl rfl
    (hasType_TP constants_T Γ) hm hm (by decide)
    (.inl (by simp [VLevel.IsNeverZero, VLevel.inst, VLevel.eval, cxInfo]))

private theorem hasType_body (Γ : List VExpr) :
    cxEnv.HasType 0 (cxT :: Γ)
      (.forallE (.app (.proj `T 0 (.bvar 0)) (.bvar 0)) VExpr.false) (.sort .zero) := by
  have happ : cxEnv.HasType 0 (cxT :: Γ) (.app (.proj `T 0 (.bvar 0)) (.bvar 0))
      (.sort .zero) :=
    .appDF (hasType_proj (.bvar .zero)) (.bvar .zero)
  exact toProp (by simp [VLevel.WF]) (by simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax])
    (.forallEDF happ (hasType_false _ _))

private theorem hasType_D (Γ : List VExpr) : cxEnv.HasType 0 Γ cxD cxTP :=
  .lamDF (hasType_T constants_T Γ) (hasType_body Γ)

private theorem hasType_M (Γ : List VExpr) : cxEnv.HasType 0 Γ cxM cxT := by
  have hmk : cxEnv.HasType 0 Γ (.const `mk []) (.forallE cxTP cxT) :=
    .constDF (ci := cxMkVal.toVConstant) constants_mk (by simp) (by simp) rfl .nil
  exact .appDF hmk (hasType_D Γ)

private theorem hasType_P (Γ : List VExpr) : cxEnv.HasType 0 Γ cxP (.sort .zero) :=
  .appDF (hasType_D Γ) (hasType_M Γ)

/-- `P ≡ (P → False) : Prop`, by `beta` and `projIota`. -/
private theorem defEq_P (Γ : List VExpr) :
    cxEnv.IsDefEq 0 Γ cxP (.forallE cxP VExpr.false) (.sort .zero) := by
  have hbeta : cxEnv.IsDefEq 0 Γ cxP
      (.forallE (.app (.proj `T 0 cxM) cxM) VExpr.false) (.sort .zero) :=
    .beta (hasType_body Γ) (hasType_M Γ)
  have hiota : cxEnv.IsDefEq 0 Γ (.proj `T 0 cxM) cxD cxTP :=
    .projIota (info := cxInfo) (levels := []) (args := [cxD]) projections_T
      (hasType_proj (hasType_M Γ)) rfl (hasType_D Γ)
  have happ : cxEnv.IsDefEq 0 Γ (.app (.proj `T 0 cxM) cxM) cxP (.sort .zero) :=
    .appDF hiota (hasType_M Γ)
  exact hbeta.trans <|
    toProp (by simp [VLevel.WF]) (by simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax])
      (.forallEDF happ (hasType_false _ _))

private theorem hasType_omega (Γ : List VExpr) :
    cxEnv.HasType 0 Γ cxOmega (.forallE cxP VExpr.false) := by
  have hvar : cxEnv.HasType 0 (cxP :: Γ) (.bvar 0) cxP := .bvar .zero
  have hbody : cxEnv.HasType 0 (cxP :: Γ) (.app (.bvar 0) (.bvar 0)) VExpr.false :=
    .appDF (.defeqDF (defEq_P _) hvar) hvar
  exact .lamDF (hasType_P Γ) hbody

/-- `ω ω : False` in `cxEnv`. This uses the typing rules only, not how `cxEnv` was reached. -/
theorem cxEnv_proves_false :
    cxEnv.HasType 0 [] (.app cxOmega cxOmega) VExpr.false :=
  .appDF (hasType_omega []) (.defeqDF (.symm (defEq_P [])) (hasType_omega []))

/-- The two axioms `T` and `mk` give `cxEnvCtors`, the environment `cxEnv` without its projection
entry. -/
theorem wf_cxEnvCtors : VEnv.WF' [.axiom cxMkVal, .axiom cxTypeVal] cxEnvCtors := by
  refine .decl (.axiom ?_ (rfl : cxEnvT.addConst _ _ = some cxEnvCtors))
    (.decl (.axiom ?_ (rfl : VEnv.empty.addConst _ _ = some cxEnvT)) .empty)
  · exact ⟨_, .forallEDF (hasType_TP (by simp [cxEnvT]) []) (hasType_T (by simp [cxEnvT]) _)⟩
  · exact ⟨_, .sortDF (by trivial) (by trivial) rfl⟩

/-- A well-formed environment whose history lists no inductive declaration has no projection
entry. -/
theorem not_projections_of_no_induct {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env)
    (hds : ∀ decl, VDecl.induct decl ∉ ds) (name : Name) (info : VProjectionInfo) :
    ¬ env.projections name info := by
  intro hp
  obtain ⟨D, _, hD, _⟩ := H.projection_formation hp
  exact hds D hD

/-- No history without an inductive declaration reaches `cxEnv`. In particular the two axioms
`T` and `mk` do not: `¬ VEnv.WF' [.axiom cxMkVal, .axiom cxTypeVal] cxEnv`. -/
theorem not_wf_cxEnv_of_no_induct {ds : List VDecl} (hds : ∀ decl, VDecl.induct decl ∉ ds) :
    ¬ VEnv.WF' ds cxEnv :=
  fun H => not_projections_of_no_induct H hds _ _ projections_T

theorem not_wf_cxEnv_of_axioms : ¬ VEnv.WF' [.axiom cxMkVal, .axiom cxTypeVal] cxEnv :=
  not_wf_cxEnv_of_no_induct (by simp)

/-- Every well-formed history of `cxEnv` lists an inductive declaration `D` that registers `T`
as a structure with constructor `mk : (T → Prop) → T` and satisfies the source and formation
judgments over a well-formed environment below `cxEnv`. -/
theorem wf_cxEnv_formation {ds : List VDecl} (H : VEnv.WF' ds cxEnv) :
    ∃ D base, VDecl.induct D ∈ ds ∧ base.WF ∧ base ≤ cxEnv ∧
      D.SourceWF base ∧ D.FormationWF base ∧ ⟨`T, cxInfo⟩ ∈ D.projectionEntries := by
  obtain ⟨D, base, hD, hbase, hle, hsource, hformation, entry, hentry, hname, hinfo⟩ :=
    H.projection_formation projections_T
  refine ⟨D, base, hD, hbase, hle, hsource, hformation, ?_⟩
  obtain ⟨typeName, info⟩ := entry
  cases hname
  cases hinfo
  exact hentry

/-- The type formers and constructors of a constructor-and-projection prefix are not constants
of the environment it extends. So the prefix never reinterprets an axiom, a definition or an
opaque constant as a structure. -/
theorem projectionStage_sourceNames_fresh {env env' : VEnv} {decl : VInductDecl}
    (h : decl.ProjectionStage env env') :
    ∀ name ∈ decl.sourceNames, env.constants name = none := by
  obtain ⟨envTypes, envCtors, htypes, hctors, -⟩ := h.stages
  intro name hname
  simp only [VInductDecl.sourceNames, List.mem_append, List.mem_map] at hname
  rcases hname with ⟨ci, hci, rfl⟩ | ⟨ci, hci, rfl⟩
  · exact VEnv.addConstVals_names_fresh htypes ci hci
  · have hfresh := VEnv.addConstVals_names_fresh hctors ci hci
    cases hc : env.constants ci.name with
    | none => rfl
    | some a =>
      rw [(VEnv.addConstVals_le htypes).constants hc] at hfresh
      cases hfresh

private theorem hasType_sort (env : VEnv) :
    env.HasType 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  .sortDF (by trivial) (by trivial) rfl

private theorem cxMkVal_wf : cxMkVal.toVConstant.WF cxEnvT :=
  ⟨_, .forallEDF (hasType_TP (by simp [cxEnvT]) []) (hasType_T (by simp [cxEnvT]) _)⟩

private theorem cxDecl_rawCtorShape (b : Bool) :
    ∀ type ∈ (cxDecl b).types, ∀ ctor ∈ type.ctors, (cxDecl b).RawCtorShape type ctor := by
  intro type htype ctor hctor
  obtain rfl : type = cxType := by simpa [cxDecl] using htype
  obtain rfl : ctor = cxMkVal := by simpa [cxType] using hctor
  refine ⟨[cxTP], cxT, rfl, Nat.zero_le _, ?_, rfl⟩
  exact ⟨_, List.mem_singleton.2 rfl, .inr rfl, [], rfl, rfl, rfl, rfl⟩

/-- The source judgment holds for either flag: the header and the constructor type are typed
and the names are distinct. -/
theorem cxDecl_sourceWF (b : Bool) : (cxDecl b).SourceWF .empty := by
  refine ⟨by simp [cxDecl], by simp [VInductDecl.sourceNames, VInductDecl.typeConstants,
    VInductDecl.constructorConstants, cxDecl, cxType, cxMkVal], ?_, ?_, cxEnvT, cxEnvCtors, rfl,
    rfl, ?_, ?_⟩
  · intro type htype
    obtain rfl : type = cxType := by simpa [cxDecl] using htype
    rfl
  · intro ctor hctor
    obtain rfl : ctor = cxMkVal := by
      simpa [VInductDecl.constructorConstants, cxDecl, cxType] using hctor
    rfl
  · intro type htype
    obtain rfl : type = cxType := by simpa [cxDecl] using htype
    exact ⟨_, hasType_sort _⟩
  · intro ctor hctor
    obtain rfl : ctor = cxMkVal := by
      simpa [VInductDecl.constructorConstants, cxDecl, cxType] using hctor
    exact cxMkVal_wf

/-- Stages 0 to 2 of `VEnv.addInduct` take the empty environment to `cxEnv`, for either flag. -/
theorem cxDecl_install (b : Bool) : (cxDecl b).addTypesCtorsProjs .empty = some cxEnv := rfl

/-- For the declaration `T`, `mk : (T → Prop) → T` over the empty environment, the formation
judgment is the only premise of the constructor-and-projection prefix that is in question. -/
theorem cxDecl_projectionStage_iff (b : Bool) :
    (cxDecl b).ProjectionStage .empty cxEnv ↔ (cxDecl b).FormationWF .empty :=
  ⟨fun h => h.formation, fun h => ⟨cxDecl_sourceWF b, h, cxDecl_install b⟩⟩

/-- With `isUnsafe = true` formation holds: the universe bound is met and positivity of the
field `T → Prop` is not asked for. -/
theorem cxDecl_unsafe_formationWF : (cxDecl true).FormationWF .empty := by
  have hT : cxEnvT.constants `T = some cxTypeVal.toVConstant := by simp [cxEnvT]
  refine .ordinary ⟨[], .succ .zero, cxEnvT, rfl, ?_, ?_, cxDecl_rawCtorShape true⟩
  · intro type htype
    obtain rfl : type = cxType := by simpa [cxDecl] using htype
    exact ⟨by simp [VLevel.equiv_def, cxType],
      .sort (.succ .zero), [], .sort (.succ .zero), [], .sort (.succ .zero), _,
      hasType_sort _, rfl, rfl, .zero, hasType_sort _⟩
  · intro type htype ctor hctor
    obtain rfl : type = cxType := by simpa [cxDecl] using htype
    obtain rfl : ctor = cxMkVal := by simpa [cxType] using hctor
    refine ⟨⟨[], _, rfl, .zero⟩, .forallE cxTP cxT, [], .forallE cxTP cxT, _, [],
      .forallEDF (hasType_TP hT []) (hasType_T hT _), rfl, .zero, .zero, ?_⟩
    refine .field (hasType_TP hT []) (.inr ?_) (.inl rfl) (hasType_TP hT [])
      (hasType_T hT _) (.result ?_ (hasType_T hT _))
    · intro ls
      simp [cxType, VLevel.eval, Lean.Nat.imax]
    · exact ⟨_, List.mem_singleton.2 rfl, .inr rfl, [], rfl, rfl, rfl, rfl, by simp⟩

/-- An environment whose history is one inductive declaration, flagged unsafe and without
recursors, is well formed and has a closed term of type `∀ (p : Prop), p`. No axiom is
declared. The entry is the constructor-and-projection prefix of the declaration
(`VEnv.WF'.inductProjections`), which does not need the recursors of a non-positive
declaration to exist. -/
theorem wf_unsafe_projectionStage_proves_false :
    ∃ (decl : VInductDecl) (env : VEnv), VEnv.WF' [.induct decl] env ∧ decl.isUnsafe = true ∧
      ∃ e, env.HasType 0 [] e VExpr.false :=
  ⟨cxDecl true, cxEnv,
    .inductProjections ((cxDecl_projectionStage_iff true).2 cxDecl_unsafe_formationWF) .empty,
    rfl, _, cxEnv_proves_false⟩

end Lean4LeanModel
