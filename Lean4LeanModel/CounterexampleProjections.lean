import Lean4LeanModel.Semantics
import Lean4Lean.Theory.Typing.Env

/-!
# The projection stage of `VEnv.WF'` proves `False` from two axioms

`VEnv.WF'.inductProjections` registers projection entries for a structure whose type former and
constructor are already constants of a well-formed environment. Its premises are shape conditions
only: no strict positivity is required, and the constants need not come from an `induct`
declaration. So the two axioms `T : Type` and `mk : (T → Prop) → T` can be registered as a
structure, after which `projIota` gives `(mk d).1 ≡ d`. With `d := fun t => t.1 t → False`,
`m := mk d` and `P := d m`, this yields `P ≡ (P → False) : Prop`, and the usual self-application
`(fun h : P => h h) (fun h : P => h h)` is a closed term of type `VExpr.false`.

Nothing in the model depends on this module; it records a checked fact about the theory.
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

/-- The non-positive "structure" declaration whose projection entries are registered. -/
def cxDecl : VInductDecl where
  uvars := 0
  nparams := 0
  isUnsafe := false
  recs := []
  types := [{ name := `T, uvars := 0, type := .sort (.succ .zero), numIndices := 0,
              resultLevel := .succ .zero, ctors := [cxMkVal] }]

/-- The block read off `cxDecl`, without recursors or rules. -/
def cxBlock : VInductBlock :=
  ⟨cxDecl.typeConstants, cxDecl.constructorConstants, [], [], cxDecl.projectionEntries⟩

/-- The projection metadata registered for `T`. -/
def cxInfo : VProjectionInfo where
  uvars := 0
  nparams := 0
  nindices := 0
  resultLevel := .succ .zero
  ctorName := `mk
  ctorType := .forallE cxTP cxT

/-- The environment after `axiom T : Type`. -/
def cxEnvT : VEnv :=
  { VEnv.empty with
    constants := fun n => if `T = n then some cxTypeVal.toVConstant else VEnv.empty.constants n }

/-- The environment after `axiom T : Type` and `axiom mk : (T → Prop) → T`. -/
def cxEnvCtors : VEnv :=
  { cxEnvT with
    constants := fun n => if `mk = n then some cxMkVal.toVConstant else cxEnvT.constants n }

/-- The environment after the projection stage. -/
def cxEnv : VEnv := cxEnvCtors.addProjections cxBlock.projections

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
    simp [cxBlock, VInductDecl.projectionEntries, cxDecl, cxInfo, cxMkVal], rfl, rfl⟩)

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

/-- `ω ω : False` in the environment after the projection stage. -/
theorem cxEnv_proves_false :
    cxEnv.HasType 0 [] (.app cxOmega cxOmega) VExpr.false :=
  .appDF (hasType_omega []) (.defeqDF (.symm (defEq_P [])) (hasType_omega []))

/-- The environment before the projection stage is the one reached by the two axioms `T` and
`mk` alone, and it is the `envCtors` to which the projection entries are added. -/
theorem wf_cxEnvCtors :
    VEnv.WF' [.axiom cxMkVal, .axiom cxTypeVal] cxEnvCtors ∧
      cxEnv = cxEnvCtors.addProjections cxDecl.projectionEntries := by
  refine ⟨.decl (.axiom ?_ (rfl : cxEnvT.addConst _ _ = some cxEnvCtors))
    (.decl (.axiom ?_ (rfl : VEnv.empty.addConst _ _ = some cxEnvT)) .empty), rfl⟩
  · exact ⟨_, .forallEDF (hasType_TP (by simp [cxEnvT]) []) (hasType_T (by simp [cxEnvT]) _)⟩
  · exact ⟨_, .sortDF (by trivial) (by trivial) rfl⟩

/-- The projection stage applies to the two axioms: its premises hold for `cxDecl` over the empty
base, so `cxEnv` is well formed with the history of `cxEnvCtors`. -/
theorem wf_cxEnv : VEnv.WF' [.axiom cxMkVal, .axiom cxTypeVal] cxEnv := by
  have hsort : ∀ env : VEnv,
      env.HasType 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := fun _ =>
.sortDF (by trivial) (by trivial) rfl
  have hmkWF : cxMkVal.toVConstant.WF cxEnvT :=
    ⟨_, .forallEDF (hasType_TP (by simp [cxEnvT]) []) (hasType_T (by simp [cxEnvT]) _)⟩
  have hraw : ∀ type ∈ cxDecl.types, ∀ ctor ∈ type.ctors, cxDecl.RawCtorShape type ctor := by
    intro type htype ctor hctor
    obtain rfl : type = _ := by simpa [cxDecl] using htype
    obtain rfl : ctor = cxMkVal := by simpa using hctor
    refine ⟨[cxTP], cxT, rfl, Nat.zero_le _, ?_, rfl⟩
    exact ⟨_, List.mem_singleton.2 rfl, .inr rfl, [], rfl, rfl, rfl, rfl⟩
  refine .inductProjections (base := .empty) (envTypes := cxEnvT) (decl := cxDecl)
    (block := cxBlock) .empty wf_cxEnvCtors.1 (by simp [VInductDecl.sourceNames,
      VInductDecl.typeConstants, VInductDecl.constructorConstants, cxDecl, cxMkVal])
    ?_ ?_ ?_ ?_ hraw rfl rfl rfl rfl rfl
  · intro type htype
    obtain rfl : type = _ := by simpa [cxDecl] using htype
    exact ⟨_, hsort _⟩
  · intro ctor hctor
    obtain rfl : ctor = cxMkVal := by
      simpa [VInductDecl.constructorConstants, cxDecl] using hctor
    rfl
  · intro ctor hctor
    obtain rfl : ctor = cxMkVal := by
      simpa [VInductDecl.constructorConstants, cxDecl] using hctor
    exact hmkWF
  · refine ⟨[], cxEnvT, rfl, ?_, ?_, hraw⟩
    · intro type htype
      obtain rfl : type = _ := by simpa [cxDecl] using htype
      exact ⟨.sort (.succ .zero), [], .sort (.succ .zero), [], .sort (.succ .zero), _,
        hsort _, rfl, rfl, .zero, hsort _⟩
    · intro type htype ctor hctor
      obtain rfl : type = _ := by simpa [cxDecl] using htype
      obtain rfl : ctor = cxMkVal := by simpa using hctor
      exact ⟨[], _, rfl, .zero⟩

/-- A well-formed environment whose history consists of exactly the two axioms `T` and `mk` has a
closed term of type `∀ (p : Prop), p`: the projection stage adds no declaration to the history
and requires no positivity of the structure it registers. -/
theorem wf_inductProjections_proves_false :
    ∃ (ds : List VDecl) (env : VEnv), VEnv.WF' ds env ∧
      (∀ d ∈ ds, ∃ ci, d = .axiom ci) ∧ ds.length = 2 ∧
      ∃ e, env.HasType 0 [] e VExpr.false := by
  refine ⟨_, cxEnv, wf_cxEnv, ?_, rfl, _, cxEnv_proves_false⟩
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl <;> exact ⟨_, rfl⟩

end Lean4LeanModel
