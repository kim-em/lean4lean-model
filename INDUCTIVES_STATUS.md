# The model against the lean4lean theory of PR 54

This branch (`model/inductives-on-iota`, on top of `model/quotients`) makes the model build against
the typing judgment of lean4lean PR 54, "inductives on iota"
(https://github.com/digama0/lean4lean/pull/54). It does not construct the model of inductive
types. It adapts everything that can be adapted without that construction, and reduces the rest to
the list in section 5.

File and line references of the form `Theory/...:n` are to `Lean4Lean/Theory/...` at the pinned
lean4lean revision.

## 1. Pins

| | old (`model/quotients`) | now |
|---|---|---|
| lean4lean | `digama0/lean4lean` `master`, `779c51fd` | `kim-em/lean4lean` `agent/inductives-on-iota`, `b5944782aeec1ccffb041da7ab1331fcc855aef2` |
| Lean | `v4.32.2` | `v4.33.0-rc2` |
| Mathlib | `v4.32.2` | `v4.33.0-rc2` (`51e6992e`) |
| batteries | `023ce7d6` | `76e1c118` |

Mathlib `v4.33.0-rc2` resolves batteries to `76e1c118`, which is exactly the revision lean4lean's
own `v4.33.0-rc2` pin resolves to, so the Mathlib olean cache is valid (`lake exe cache get`
downloads nothing that has to be rebuilt).

## 2. Build status

`lake build` succeeds. `scripts/check-proof-debt.sh` passes (updated for the new counts).

There are six `sorry`s in this repository, all in `Lean4LeanModel/ModelConstructionDebt.lean`
(three more than `model/quotients`), and one upstream `sorry` that the model reaches
(`IsDefEqU.weakN_iff`, `Theory/Typing/UniqueTyping.lean:92`). There is one new explicit hypothesis,
`Assignment.RulesWF`, a field of `ModelSetup`. Section 5 lists all of them.

`#print axioms` (`Lean4LeanModel/TrustAudit.lean`): `consistency`, `quotDefEq_valid` and
`model_addQuot_canonical` depend on `sorryAx`. `quotConstValue_valid`, `quotMkConstValue_valid`,
`quotLiftConstValue_valid` and `quotIndConstValue_valid` no longer do: at the old pin they reached
upstream `sorry`s that PR 54 has proved (unique typing).

Version drift cost nothing: no proof needed changing for Lean or Mathlib. The only non-theory
changes are two renames inside lean4lean (`Nat.imax` is now `Lean.Nat.imax`; `IsDefEqU.sort_inv`
moved to `Theory/Typing/Injectivity.lean`).

## 3. What changed in the theory that the model consumes

Relative to the old pin `779c51fd`:

1. `VExpr.proj typeName index struct` (`Theory/VExpr.lean:12`): a primitive projection.
2. `VEnv` has two new components (`Theory/VEnv.lean:12`, `:15`): `pats`, a registry of schematic
   reduction rules keyed by a `Pattern`, and `projections`, the projection metadata of the
   registered structures. `VEnv.LE` compares all four components.
3. `IsDefEq` (`Theory/Typing/Basic.lean`) has five new rules:
   * `projDF` (`:36`): typing and congruence of a projection. The major premise is typed at
     `S levels (params ++ indexArgs)`; the field type is computed from the constructor type by
     `VProjectionInfo.fieldType`; the guard is
     `(info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero`.
   * `pat` (`:78`): ι reduction. A term matching a registered pattern equals its reduct. The rule
     carries the typing of the redex and of the reduct at a common type.
   * `projIota` (`:84`): `(mk args).i ≡ args[nparams + i]`.
   * `structEta` (`:91`): `mk params (e.0) ... (e.(n-1)) ≡ e`, for a structure with no indices.
   * `unitLike` (`:102`): any two terms of a structure with no indices and no fields are equal.
4. `IsDefEqStrong` (`Theory/Typing/Strong.lean`) has the corresponding five rules; `OrderedStrong`
   replaces `Ordered` as the hypothesis of `IsDefEq.strong` and of the inversion lemmas.
5. `VDecl.WF` (`Theory/Typing/Env.lean`) has a `mutualDef` case (`:27`; this one is already on
   lean4lean `master`), and `induct` (`:43`) is no longer vacuous: `VInductDecl.WF`
   (`Theory/Inductive.lean:752`) and `VEnv.addInduct` (`Theory/Inductive/AddInduct.lean:90`) are
   real definitions. `addInduct` adds the type formers, the constructors, the projection entries of
   the single-constructor families (`VInductDecl.projectionEntries`,
   `Theory/DeclarationData.lean:122`), the recursors, and one `pats` entry per recursor rule
   (`VEnv.addRecRule`, `AddInduct.lean:19`).
6. `VEnv.WF'` has a second step constructor, `inductProjections` (`Theory/Typing/Env.lean:59`): the
   projection stage of an inductive declaration as a history step of its own.
7. Unique typing and sort injectivity are proved. Context strengthening
   (`IsDefEqU.weakN_iff`) is the one open proof of PR 54, and its `OPEN_PROOFS.md` says it is not
   known to be true.

The quotient rules are still stored definitional equations (`VEnv.defeqs`, the `extra` rule), so
the quotient part of the model is untouched.

## 4. How the model was adapted

* **Semantics** (`Semantics.lean`). `Assignment` gains
  `projVal : Name → Nat → ZFSet → ZFSet`, the value of the `i`-th projection of the structure `S`
  on a structure value. `interp` gains the clause

  ```
  interp (.proj S i e) = if safeTermClass env Γ L (.proj S i e) = 0 then bullet
                         else assignment.projVal S i (interp e)
  ```

  A projection that is a proof is `bullet`, like every proof. `projVal` takes neither universe
  arguments nor parameters: the value of a data-valued structure determines its fields, and by the
  guard of `projDF` a projection out of a possibly-`Prop` structure is a proof.
* **Transport** (`Transport.lean`, `ContextConversion.lean`, `ModelConstruction.lean`). The
  structural lemmas `interp_liftN`, `interp_instN`, `interp_instL`, `interp_defeqCtx` and
  `interp_extension` get their `proj` cases, proved. They need the inversion
  `HasType.proj_inv` of lean4lean, wrapped as `wf_proj_major` and `wf_proj_registered`.
* **Rule validity** (`ModelSetup.lean`). `Assignment.RulesWF κ env assignment` has five fields,
  one per new typing rule. Each field is the semantic content of the rule for an arbitrary
  instance in a modeled context; its hypotheses are the premises of the rule and the semantic
  facts the fundamental theorem holds for those premises. `ModelSetup` gains the field
  `rulesWF`.
* **Fundamental theorem** (`Fundamental.lean`). `fundamentalStrong` has five new cases and no
  `sorry`. The congruence half of `projDF` is proved outright; the membership half and the other
  four rules are applications of the five fields of `RulesWF`.
* **History** (`ModelConstruction.lean`). `model_of_wfHistory_withAxioms` gets the `mutualDef`
  case of `VDecl.WF` and the `inductProjections` case of `VEnv.WF'`, each discharged by a boundary
  in `ModelConstructionDebt.lean`. The `def`, `opaque`, axiom and quotient steps now also have to
  re-establish `RulesWF` over the extended environment; they do it through
  `Assignment.RulesWF.extension`. The empty environment has no rules
  (`Assignment.RulesWF.of_no_rules`).
* **Two checked counterexamples** (`Counterexamples.lean`, `CounterexampleProjections.lean`):
  `wf_mutualDef_proves_false` (6.1) and `wf_inductProjections_proves_false` (6.2). Nothing in the
  model depends on them.

## 5. Debt

### 5.1 Statement changes

No theorem had its statement edited to make it compile. The following definitions changed, which
changes the meaning of every statement that mentions them:

1. `Assignment` has the new field `projVal`.
2. `interp` has the new clause for `VExpr.proj`.
3. `ModelSetup` has the new field `rulesWF : assignment.RulesWF κ env`. This strengthens
   `ModelSetup`, so it strengthens the hypothesis of `fundamental`, `fundamentalStrong` and
   `fundamental_hasType`, and the conclusion of `model_of_wf`, `model_of_wfHistory*`,
   `model_addAxiom`, `model_addQuot_sem`, `model_addQuot_canonical`, `AxiomHandler` and the three
   old boundaries. Without it `fundamental` is false at the new theory: a `ModelSetup` in the old
   sense constrains a recursor only to lie in its type.
4. `Assignment.Extends` was a `def` (a single universally quantified implication about
   `constVal`) and is now a structure with that field (`const`) and a second one (`proj`:
   `projVal` is preserved on the structures registered in `env`). It moved from
   `ModelConstruction.lean` to `ModelSetup.lean`.
5. `Nat.imax` in statements of `DependentFunction.lean` and `Universe.lean` is now spelled
   `Lean.Nat.imax` (lean4lean rename; same function).
6. Hypotheses of type `env.Ordered` are unchanged, but `fundamental` now obtains
   `OrderedStrong` from `M.envWF` internally.

`consistency` is textually unchanged. It was already refutable (arbitrary axioms); see 6.1 for a
second refutation.

### 5.2 The explicit hypothesis `Assignment.RulesWF`

`Lean4LeanModel/ModelSetup.lean`. Nothing constructs it for an environment that has a rule. Its
fields are what the interpretation of inductive types has to deliver:

| field | rule | content |
|---|---|---|
| `pat` | `IsDefEq.pat` | a typed instance `e` of a registered pattern rule and its reduct have the same value |
| `proj_mem` | `projDF` | `⟦e.i⟧ ∈ ⟦fieldType⟧` when `⟦e⟧ ∈ ⟦S levels (params ++ indexArgs)⟧` |
| `projIota` | `projIota` | `⟦(mk args).i⟧ = ⟦args[nparams + i]⟧` |
| `structEta` | `structEta` | `⟦mk params (e.0) ... (e.(n-1))⟧ = ⟦e⟧` |
| `unitLike` | `unitLike` | `⟦S levels params⟧` is a subsingleton when `S` has no fields |

Used in: the five new cases of `fundamentalStrong`, and nowhere else.

Caveat on `pat`. Its hypotheses are exactly what the induction in `fundamentalStrong` provides:
the typing of the redex and of the reduct, and the membership of their values in the type. They
do not include semantic facts about the matched subterms (that the minor premises, the fields of
the constructor and so on have values in the interpretations of their types). A proof that the
canonical recursor computes needs those facts. So before `pat` can be established, either the
induction motive of `fundamentalStrong` has to be strengthened to carry semantic typing down
application spines (a change inside this repository), or `IsDefEqStrong.pat` has to carry the
typing of the matched arguments (an upstream change). Section 8 takes the first route.

### 5.3 The six `sorry`s (`Lean4LeanModel/ModelConstructionDebt.lean`)

1. **`Assignment.RulesWF.extension`** (new). If `env ≤ env'` registers no new pattern rule and no
   new projection entry, and `assignment'` extends `assignment`, then `RulesWF` for `env` gives
   `RulesWF` for `env'`.
   Used by: `ModelSetup.of_addConst`, `ModelSetup.of_addDefEq` (so by the `def`, `opaque` and
   axiom steps) and `model_addQuot_sem`.
   Assessment: believed true where it is used, but probably not provable from the instance-wise
   hypothesis alone, because the instances over `env'` whose matched subterms mention new
   constants are not instances over `env`. It should disappear, not be proved: once `RulesWF` is
   derived from a structural invariant (each installed block interpreted by its canonical
   fixpoint), that invariant is preserved by a rule-free extension by `interp_extension` and the
   instance-wise statement follows in every extension.
2. **`model_axiom_boundary`** (old). Known false: arbitrary axioms. Only feeds the unrestricted
   `model_of_wfHistory`.
3. **`model_mutualDef_boundary`** (new). Known false: see 6.1. Used by the `mutualDef` case of
   `model_of_wfHistory_withAxioms`.
   A true statement restricts the block. A block in which no value mentions a constant of the
   block is a sequence of `opaque` steps followed by `addDefEq`s and can be proved with what is
   there. Nothing weaker than a termination argument works for recursive blocks, and the kernel
   only uses these blocks for `unsafe` and `partial` definitions.
4. **`model_inductive_boundary`** (old statement, new content). `decl.WF env` and
   `env.addInduct decl = some env'` give a `ModelSetup` for `env'`. At the old pin this was blocked
   on upstream `sorry` definitions; now it is the real theorem. Not provable as stated, because
   `decl.WF` admits `isUnsafe = true` declarations (6.3); with the hypothesis
   `decl.isUnsafe = false` it is the main theorem of the remaining work. Section 7 says what the
   proof needs.
5. **`model_inductProjections_boundary`** (new). Known false in general: see 6.2. Used by the
   `inductProjections` case of `model_of_wfHistory_withAxioms`.
6. **`model_quotient_boundary`** (old). Unchanged: needs the canonical meaning of `Eq`
   (`Assignment.ModelsEq`) as an invariant of the history induction, which the inductive
   construction supplies. `model_addQuot_canonical` is the proved step that consumes it.

### 5.4 Upstream

`IsDefEqU.weakN_iff` (`Theory/Typing/UniqueTyping.lean:92`), through `Lean4LeanModel/Upstream.lean`
(`ctx_of_liftN`, `hasType_liftN_sort_iff`, `strengthen_liftN_typing`). The model uses it to show
that the syntactic proof/data classifiers `typeClass` and `termClass` are invariant under
weakening, which `interp_liftN` needs. lean4lean's `OPEN_PROOFS.md` reports a countermodel
argument for well-formed environments without `Eq` and no proof with it. The model uses less than
the full statement: only that a term whose lift is typed is itself typed, with the same sort class.
If `weakN_iff` stays open, the model should stop depending on it, for instance by classifying
terms through a typing-independent syntactic invariant, or by proving that special case directly.

## 6. Findings about the PR 54 definitions, from the model's side

The consistency theorem cannot be stated over `VEnv.WF`, even after restricting axioms. Three
separate features of `VEnv.WF` admit environments without a model.

### 6.1 `mutualDef` blocks (`Theory/Typing/Env.lean:27`; already on lean4lean `master`)

A block's values are typed in the environment that already contains the block's constants, with
no termination condition. `Lean4LeanModel.wf_mutualDef_proves_false` proves, with no `sorry`:
there is an environment with history `[.mutualDef [loop]]`, where
`loop : ∀ (p : Prop), p := loop`, that is `VEnv.WF'` and has a closed term of type `VExpr.false`.
No axiom is declared.

### 6.2 `VEnv.WF'.inductProjections` (`Theory/Typing/Env.lean:59`; new in PR 54)

The constructor registers the projection entries of `decl` on top of an environment `envCtors`
that is itself `WF'` and equals a `WF'` base plus the type formers and constructors of `decl`.
Its premises are `sourceNames.Nodup`, the typing of the headers and constructor types,
`SourceParameterWF` and `RawCtorShape` (`Theory/Inductive/SourceShape.lean:144`, `:156`). None of
them is positivity or a universe bound, and none says the type formers and constructors were
installed by an inductive declaration. Since `addInduct` always installs recursors as well, in a
history they can only have been declared by `axiom` or `opaque` steps. So `VEnv.WF` contains
environments in which an axiomatized type and constructor carry `projIota`, `structEta` and
`unitLike`.

Counterexample, proved with no `sorry` as
`Lean4LeanModel.wf_inductProjections_proves_false`: `axiom T : Type`,
`axiom mk : (T → Prop) → T`, then the projection stage for the one-family declaration
`T` with constructor `mk` (`isUnsafe := false`, no recursors). All premises are shape conditions
that this declaration satisfies. In the resulting environment `projIota` gives `(mk d).0 ≡ d`, and
with `d := fun t => (t.0 t → ∀ p : Prop, p)` the proposition `P := d (mk d)` satisfies
`P ≡ (P → ∀ p, p)`, from which `(fun h : P => h h) (fun h : P => h h) : ∀ p : Prop, p`. The
history of that environment is the two axioms and nothing else.

This one costs lean4lean nothing (arbitrary axioms already make `VEnv.WF` environments
inconsistent) but it matters here in two ways:

* the standard-axioms theorem `model_of_wfHistory_standard` restricts axioms, and the projection
  stage adds nothing to the history list, so the restriction does not see it. With only standard
  axioms the type former and constructor must be `opaque`, and an opaque type has no closed
  inhabitants, so I do not have a refutation in that case; but
* the model interprets an `opaque` constant by its stored value, and a later projection stage
  then demands that this value behave like a free structure. `opaque T : Type := Prop` and
  `opaque mk : (∀ X : Type, X) → T := fun h => h T`, followed by the projection stage, need
  `⟦T⟧ = ∅` (the field type is empty and `proj_mem` maps `⟦T⟧` into it), while the model built for
  the history so far has `⟦T⟧ = ⟦Prop⟧`. So the model of the extended environment is not an
  extension of the model in hand, and the history induction as structured cannot do this step.

The cleanest resolution is for the target theorem to range over histories that do not use
`inductProjections` (section 8, step 0). An inductive declaration does not need it:
`VDecl.WF.induct` installs the projections itself.

### 6.3 `isUnsafe` declarations (`Theory/Inductive/Formation.lean:300`; new in PR 54)

`VInductDecl.CtorTailWF.field` requires `decl.isUnsafe = true ∨ decl.Positive env ctx depth dom`.
`VInductDecl.WF` does not require `isUnsafe = false`, and `VDecl.WF.induct` takes any
`decl.WF env`. So non-positive declarations flagged unsafe are well-formed history steps. A nested
declaration may use an unsafe container only if it is itself unsafe
(`Theory/Inductive/Compilation.lean:73`), so safety is hereditary and the restriction
`isUnsafe = false` on the declarations of a history is enough.

### 6.4 Points that are awkward but not wrong

* The `pat` rule checks nothing about the constructor's parameters in the major premise (the
  side condition of every registered rule is `.true`, `AddInduct.lean:19`); they are tied to the
  recursor's parameters only by the typing of the redex. Constructor values in the model must
  therefore not record their parameters. The same holds for the auxiliary recursors of nested
  blocks, whose rules fire on the constructors of a container (`VInductDecl.WF.rules_ctorParams`).
* K-like reduction is not registered (`AddInduct.lean:19`, docstring). `structEta` and `unitLike`
  are the only η-style rules.
* `projDF` allows projections out of single-constructor families with indices
  (`indexArgs`); `structEta` and `unitLike` require `nindices = 0`. The kernel only projects out
  of index-free structures. Harmless for a set model.
* The projection guard `(info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero` is
  exactly what a proof-irrelevant model needs: data is only projected out of data.
* The recursor's elimination universe (`Instance.Admissible.elimination`,
  `Theory/Inductive/Signature.lean:114`): never-`Prop` families, or motive in `Prop`, or singleton
  elimination (`SingletonElimination`, `:86`: at most one constructor, every field a proof or
  among the indices) with a free target universe. This matches section 2.6 of the thesis.
* Families whose sort is sometimes `Prop` (`Sort u`) are admitted with the field-level bound
  `target.resultLevel ≈ .zero ∨ fieldLevel ≤ target.resultLevel` (`Formation.lean:299`). The model
  already dispatches on the evaluated universe arguments (`constVal c ns`), so the two regimes can
  be interpreted separately.

## 7. What `model_inductive_boundary` needs

Given `decl.WF env`, `decl.isUnsafe = false`, and a `ModelSetup` for `env`, supply `constVal` for
the type formers, constructors and recursors, `projVal` for the structures, and prove
`Assignment.WF` and `Assignment.RulesWF` for `env'`.

**What the thesis does.** As I recall chapter 6 of *The Type Theory of Lean* (not re-read for this
report; check before relying on it): universes are `V_κ` for a sequence of inaccessibles, `Prop`
is `{∅, {•}}` with proofs erased to `•` (the "proof splitting" this repository already
implements), and an inductive family is the least fixed point of the monotone operator given by
its constructors, obtained by transfinite iteration and placed in the right universe by
inaccessibility; recursors are defined by recursion on that fixed point, and large elimination
out of `Prop` is justified by the subsingleton criterion. The thesis treats one family of
(possibly mutual, indexed) inductive specifications and reduces nested inductives to mutual ones
by a syntactic translation, which is also what PR 54 does (`NestedFormationWF`, "containers",
restoration).

**A construction suited to ZFC and to PR 54.**

1. *Encoding.* A constructor value is a tagged tuple `⟨tag, field₀, …⟩` of its non-parameter
   arguments; a functional field is a `ZFSet` function graph. Parameters are not recorded (6.4).
   With this encoding every structurally smaller value lies in the transitive closure of `∈` of
   the value.
2. *Type formers.* For a block with parameters `p`, the family `i ↦ ⟦I p i⟧` is the least
   fixed point of the operator
   `F(X)(i) = { ⟨tag_c, fields⟩ | fields ∈ ⟦telescope of c⟧ with recursive occurrences read in X,
   and the indices of c at these fields are i }`.
   `F` is monotone because recursive occurrences are strictly positive, and it is a polynomial
   functor (an indexed container), so its least fixed point is the indexed W-type. Mathlib has
   `WType` and `PFunctor` at the level of types but nothing for `ZFSet`; what is needed is small
   and specific: least fixed points of `ZFSet`-valued monotone operators by iteration to a regular
   cardinal, and a bound on rank. Universe membership: every arity is the cardinality of a set in
   `V_{κ n}`, `κ n` is regular, so the iteration closes at a stage below `κ n` and the result is in
   `ModelUniverse κ n`. `DependentFunction.lean` already has the corresponding closure arguments
   for Π.
3. *Recursors.* Define the recursor value by `∈`-recursion on the major premise: read the tag,
   apply the corresponding minor premise to the fields and to the recursive results. Because
   smaller values are `∈`-below, one well-founded recursion serves ordinary, mutual, reflexive
   (functional recursive fields) and nested blocks. ι (`RulesWF.pat`) is then the unfolding
   equation of that recursion, and the typing of the recursor value (`const_mem`) is an induction
   over the fixed point.
4. *Projections.* `projVal S i x` is the `i`-th component of the tuple. `projIota` is the
   component equation, `structEta` is surjective pairing for a one-constructor family, `unitLike`
   is the fact that a one-constructor family with no fields is `{⟨tag⟩}`, and `proj_mem` is the
   typing of components (by induction along `VProjectionInfo.fieldType`, which substitutes earlier
   projections for earlier fields).
5. *`Prop`-valued families.* Interpret the family twice: the data fixed point `I♯` as above, and
   `⟦I p i⟧ = {•}` if `I♯ p i` is nonempty, `∅` otherwise. Constructors are `•`. A recursor into
   `Prop` is `•`, and its typing is an induction on `I♯`. For singleton elimination the recursor
   must return `minor fields`: the data fields are recovered from the index values (each is a
   variable among the constructor's indices), the proof fields are `•`, and recursive results are
   defined by recursion on any witness in `I♯`; that the result does not depend on the witness is
   an induction using exactly the `SingletonElimination` condition. `Acc` is the test case.
6. *Sometimes-`Prop` families.* Dispatch on the evaluated universe arguments, as `interp` already
   does for Π.
7. *Nested blocks.* PR 54 expands a nested declaration to an ordinary mutual block with
   auxiliary families that are parameter specializations of earlier containers, and installs the
   source constants with recursors whose auxiliary rules fire on the container's constructors.
   Semantically no auxiliary family is needed: with the encoding of step 1 the canonical
   interpretation of a container is monotone in a strictly positive parameter as a set operator
   (`X ⊆ Y` gives `⟦List⟧ X ⊆ ⟦List⟧ Y`), so `⟦Tree⟧` is the least fixed point of
   `X ↦ { ⟨node, l⟩ | l ∈ ⟦List⟧ X }` directly, and the auxiliary recursor is defined by the same
   `∈`-recursion as in step 3. What has to be proved is that the container's interpretation is the
   canonical one (the structural invariant of 5.3 item 1) and monotone in that parameter. The
   syntactic side, that a nested occurrence is a container applied to positive arguments, is
   available from `NestedFormationWF` and `VEnv.InstalledBelow`.
8. *From syntax to the operator.* The hard part is not set theory but reading the operator `F` off
   the declaration. `Positive` and `CtorTailWF` are stated modulo definitional equality (each field
   is positive after a conversion step), and the recursor types and rules are whatever the
   generator outputs (`RecsCompiled`). PR 54 has a normalized form, `InductiveSignature`
   (`Theory/Inductive/Signature*.lean`), from which the generator is defined; the model should
   interpret signatures, and use the existing lean4lean lemmas relating a declaration to its
   signature, instead of working with raw constructor types.

## 8. Proposed order of attack

0. **Fix the target.** Define the histories the theorem ranges over: axioms among the standard
   three, no `mutualDef` (or only non-recursive blocks), `induct` only with `isUnsafe = false`, no
   `inductProjections`. Either as a predicate on a separate inductive `SafeWF'` in this repository
   with a map to `VEnv.WF'`, or upstream. State `consistency` for it. This removes the three
   false boundaries (items 2, 3, 5 of 5.3) and makes item 4 provable.
1. **Strengthen the motive of `fundamentalStrong`** so that it carries semantic typing along
   application spines (5.2, caveat). Check on paper that `symm`, `trans` and `defeqDF` preserve the
   stronger motive before building on it.
2. **Set-theoretic library, no syntax**: tagged tuples; least fixed points of monotone operators
   on families of sets with a rank bound and universe closure; the `∈`-recursion combinator and
   its unfolding equation.
3. **One non-indexed, non-recursive data structure** end to end (for example `Prod`): type former,
   constructor, recursor, ι, and the four projection rules. This fixes the shape of the
   structural invariant that replaces `RulesWF` and removes `RulesWF.extension` (item 1 of 5.3).
4. **Signatures**: parameters, indices, recursive and reflexive fields, mutual blocks, for
   never-`Prop` families. `Nat`, `List`, `Eq`-shaped families in `Type`, `W`.
5. **`Prop`-valued families** and singleton elimination; then sometimes-`Prop` families.
   `Eq` gets its canonical meaning here, which closes `model_quotient_boundary` (item 6 of 5.3)
   through the existing `model_addQuot_canonical`, and supplies the `StandardAxiom.Handler`.
6. **Nested blocks.**
7. **`weakN_iff`**: remove the dependence (5.4), unless it is proved upstream by then.

## 9. Verified and inferred

Verified by Lean in this branch: the build; the `sorry` count and locations; the `#print axioms`
output; the proofs of the `proj` cases of the transport lemmas and of the five new cases of
`fundamentalStrong` from `RulesWF`; `wf_mutualDef_proves_false` (6.1);
`wf_inductProjections_proves_false` (6.2), whose axioms are `propext`, `Classical.choice` and
`Quot.sound`.

Verified by reading the definitions at `b5944782`, not by Lean: the `opaque` example of 6.2 (that
its two declarations and the projection stage are well formed); that `VInductDecl.WF` admits
`isUnsafe = true` (6.3; I did not construct a non-positive unsafe declaration together with its
compiled recursors, so "admits" means that no clause of `WF` mentions positivity in that case);
the items of 6.4.

Inferred: that `RulesWF.extension` is true for the extensions it is used on; that the standard-axiom
restriction leaves no refutation through `inductProjections`; the feasibility of section 7, which
is a plan and not a proof; the description of the thesis in section 7, written from memory.
