import Lean4LeanModel.Fundamental
import Lean4Lean.Theory.Typing.Env

/-!
# Explicit declaration-model boundaries

These are the only local proof holes in the construction; `INDUCTIVES_STATUS.md` at the repository
root is the full inventory. They are kept in a dedicated module so CI can reject accidental proof
debt everywhere else.

* `Assignment.RulesWF.extension`: validity of the registered ι and projection rules survives an
  environment extension that registers no rule.
* `model_axiom_boundary`: retained solely for the backwards-compatible unrestricted statement;
  `model_of_wfHistory_standard` bypasses it via explicit meanings for the standard three. False as
  stated.
* `model_mutualDef_boundary`: a block of mutually recursive definitions. False as stated.
* `model_inductive_boundary`: the set-theoretic interpretation of an inductive declaration. Needs
  the hypothesis `decl.isUnsafe = false` to be provable.
* `model_inductProjections_boundary`: the projection stage of an inductive declaration as its own
  history step. False as stated.
* `model_quotient_boundary`: the quotient mathematics and exact generated-syntax checks are
  complete, while the history step still needs the canonical equality invariant.
-/

namespace Lean4LeanModel

open Lean4Lean

universe u

/-- **Known-false statement placeholder.** The naive theorem permits arbitrary axioms, whose
declared types need not be inhabited: adding an axiom of `VExpr.false` is a counterexample. This is
the localized axiom case requested while the true statement admitting Lean's standard axioms is
being specified. -/
theorem model_axiom_boundary {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}} {ci : VConstVal}
    (M : ModelSetup κ env assignment) (hci : ci.toVConstant.WF env)
    (hadd : env.addConst ci.name ci.toVConstant = some env') (henv' : env'.WF) :
    ∃ assignment', ModelSetup κ env' assignment' := by
  sorry

/-- **Validity of the registered rules survives a rule-free extension.** If `env'` extends `env`
without registering a pattern rule or a projection entry, and `assignment'` agrees with
`assignment` on the constants and structures of `env`, then the ι and projection rules of `env`
remain valid over `env'`.

The content is that the new instances of an old rule are valid: instances whose matched subterms
mention the constants `env'` adds, or are typed through the definitional equations `env'` adds.
Constants and equations of `env` are handled by `interp_extension`; the new instances are not
instances over `env`, so this does not follow from `interp_extension`.

Believed true for the extensions it is applied to (`addConst`, `addDefEq`), but it is not known to
be provable from the instance-wise hypothesis `M.rulesWF` alone. The expected proof replaces
`Assignment.RulesWF` by a structural invariant (each installed block is interpreted by the
canonical initial algebra, each projection by the corresponding component map), which is
preserved by an extension for trivial reasons and from which the instance-wise fields follow in
every extension. -/
theorem Assignment.RulesWF.extension {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment assignment' : Assignment.{u}}
    (M : ModelSetup κ env assignment) (hle : env ≤ env') (henv' : env'.WF)
    (hpats : env'.pats = env.pats) (hprojections : env'.projections = env.projections)
    (hext : Assignment.Extends env assignment assignment')
    (hassignment' : assignment'.WF κ env') :
    assignment'.RulesWF κ env' := by
  sorry

/-- **Known-false statement placeholder.** A `mutualDef` block types every value with all the
constants of the block already declared, and no termination or productivity condition is imposed
(the kernel accepts such blocks only for `unsafe` and `partial` definitions). The singleton block
`f : ∀ (p : Prop), p := f` is well formed over any environment in which `f` is fresh, so the
resulting environment has a closed term of type `VExpr.false` and no model
(`Lean4LeanModel.wf_mutualDef_proves_false`). A true statement has
to restrict the blocks (for example to the non-recursive ones, which reduce to a sequence of
`def` steps) or exclude `mutualDef` from the histories the consistency theorem ranges over. -/
theorem model_mutualDef_boundary {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}} {cis : List VDefVal}
    (M : ModelSetup κ env assignment) (htypes : ∀ ci ∈ cis, ci.toVConstant.WF env)
    (hadd : env.addConsts cis = some env') (hvalues : ∀ ci ∈ cis, ci.WF env')
    (henv' : (env'.addDefEqs cis).WF) :
    ∃ assignment', ModelSetup κ (env'.addDefEqs cis) assignment' := by
  sorry

/-- **The model of an inductive declaration.** `env'` extends `env` by the type formers,
constructors, projection entries, recursors and ι rules of `decl` (`VEnv.addInduct`). The proof
has to supply

* values for the type formers, constructors and recursors, members of the interpretations of
  their types (`Assignment.WF.const_mem`);
* values for the projections of the structures of the block (`Assignment.projVal`);
* `Assignment.RulesWF` for `env'`: the ι rule of every recursor rule (`pat`), the four projection
  rules for the new structures, and the rules of `env` over the extended environment.

`decl.WF env` supplies the universe bounds and, for a safe declaration, strict positivity
(`formation`), the recursor types and rules as the output of the generator (`recsCompiled`), and
the typing of each ι rule (`rules_wf`). Nested declarations are admitted through a finite
expansion into an ordinary block (`VInductDecl.FormationWF.nested`).

**Not provable as stated.** `VInductDecl.CtorTailWF.field` asks for positivity of a field only
when `decl.isUnsafe = false`, so `decl.WF env` admits declarations that are not strictly positive,
and those have no model. A provable statement assumes `decl.isUnsafe = false`. -/
theorem model_inductive_boundary {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}} {decl : VInductDecl}
    (M : ModelSetup κ env assignment) (hdecl : decl.WF env)
    (hadd : env.addInduct decl = some env') (henv' : env'.WF) :
    ∃ assignment', ModelSetup κ env' assignment' := by
  sorry

/-- **Known-false statement placeholder.** `VEnv.WF'.inductProjections` registers the projection
entries of `decl` over an environment `envCtors` that is well formed and consists of a well-formed
`base` plus the type formers and constructors of `decl` as constants. Its premises are the source
judgment and the raw constructor shapes only: no strict positivity, no universe bound, and nothing
that makes the type formers and constructors those of an inductive declaration. In a history
they can only have been declared by `axiom` or `opaque` steps.

Counterexample to the statement below: `axiom T : Type` and `axiom mk : (T → Prop) → T` have a
model (`T` a singleton), and registering the projection of `T` gives `(mk d).1 ≡ d` for every
`d : T → Prop` (`projIota`). With `d := fun t => t.1 t → VExpr.false` the proposition
`d (mk d)` is definitionally equal to `d (mk d) → VExpr.false`, which yields a closed term of type
`VExpr.false`. This is checked: `Lean4LeanModel.wf_inductProjections_proves_false`.

When the type formers and constructors are `opaque` constants (the only possibility in a history
whose axioms are the standard three), the model built for `envCtors` interprets them by their
stored values, and those values need not validate the projection rules. So even where the
extended environment has a model, it is not an extension of the one in hand: `assignment'` below
cannot in general agree with `assignment` on `envCtors`. -/
theorem model_inductProjections_boundary {κ : ℕ → Cardinal.{u}}
    {base envTypes envCtors : VEnv} {assignment : Assignment.{u}}
    {decl : VInductDecl} {block : VInductBlock}
    (M : ModelSetup κ envCtors assignment) (hbase : base.WF)
    (hsource : decl.sourceNames.Nodup)
    (htypesWF : ∀ type ∈ decl.types, type.toVConstant.WF base)
    (hconstructorUvars : ∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars)
    (hctorsWF : ∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes)
    (hparams : decl.SourceParameterWF base)
    (hshape : ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors, decl.RawCtorShape type ctor)
    (htypesSource : block.types = decl.typeConstants)
    (hctorsSource : block.ctors = decl.constructorConstants)
    (hprojections : block.projections = decl.projectionEntries)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors)
    (henv' : (envCtors.addProjections block.projections).WF) :
    ∃ assignment', ModelSetup κ (envCtors.addProjections block.projections) assignment' := by
  sorry

/-- The quotient operations, their universe closure, all four exact primitive types, and the
generated `quotDefEq` computation rule are constructed and wired into the canonical `addQuot`
model step. Applying that theorem here still requires carrying `ModelsEq` through history induction.

This theorem's present signature cannot express that induction invariant: `ModelSetup` together
with `VEnv.QuotReady` says only that `Eq` is declared, not that it has the canonical semantic
meaning recorded by `ModelsEq`. Closing the boundary therefore requires strengthening the history
induction motive (or `ModelSetup`) before proving this environment step. Since canonical `Eq`
comes from the pending inductive semantics, `addQuot` is transitively blocked on that construction
even though the quotient mathematics itself is complete. -/
theorem model_quotient_boundary {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}}
    (M : ModelSetup κ env assignment) (hready : env.QuotReady)
    (hadd : env.addQuot = some env') (henv' : env'.WF) :
    ∃ assignment', ModelSetup κ env' assignment' := by
  sorry

end Lean4LeanModel
