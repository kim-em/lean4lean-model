import Lean4LeanModel.DependentFunction
import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Tower

/-!
# A universe tower from `ω` inaccessible cardinals

`universeTower`: a strictly increasing sequence of inaccessible cardinals `κ` gives a
`Lean4Lean.VEnv.Strengthening.UniverseTower`, with sets `ZFSet`, universes `V_(κ n)`, functions as
graphs, and types of the lowest universe encoded by initial segments of a well-order.
-/

namespace Lean4LeanModel

open Cardinal Ordinal Lean4Lean Lean4Lean.VEnv.Strengthening

universe u

/-- A well-order of `α` of order type the initial ordinal of its cardinality. -/
noncomputable def encRel (α : Type) : α → α → Prop := (Cardinal.exists_ord_eq α).choose

instance (α : Type) : IsWellOrder α (encRel α) := (Cardinal.exists_ord_eq α).choose_spec.choose

theorem type_encRel (α : Type) : type (encRel α) = (#α).ord :=
  (Cardinal.exists_ord_eq α).choose_spec.choose_spec.symm

/-- The encoding of an element of a type of the lowest universe: the von Neumann ordinal of its
position in `encRel`. -/
noncomputable def encZF {α : Type} (a : α) : ZFSet.{u} :=
  (Ordinal.lift.{u} (typein (encRel α) a)).toZFSet

theorem encZF_injective {α : Type} : Function.Injective (encZF.{u} (α := α)) := by
  intro a b h
  have := Ordinal.lift_inj.1 (toZFSet_injective h)
  exact (typein_injective (encRel α)) this

theorem rank_encZF_lt {α : Type} (a : α) :
    ZFSet.rank (encZF.{u} a) < (Cardinal.lift.{u} #α).ord := by
  rw [encZF, rank_toZFSet, ← Cardinal.lift_ord, Ordinal.lift_lt, ← type_encRel]
  exact typein_lt_type _ _

/-- The set of encodings of the elements of `α`. -/
noncomputable def setZF (α : Type) : ZFSet.{u} := ZFSet.range (encZF.{u} (α := α))

theorem lift_mk_lt_of_continuumSized {c : Cardinal.{u}} (hc : c.IsInaccessible) (α : Type)
    [h : ContinuumSized α] : Cardinal.lift.{u} #α < c := by
  obtain ⟨f, hf⟩ := h.out
  have h1 : #α ≤ #(ℕ → Prop) := Cardinal.mk_le_of_injective (f := f) fun a b e => hf a b e
  have h2 : #(ℕ → Prop) = 2 ^ ℵ₀ := by simp
  have h3 : Cardinal.lift.{u} #α ≤ 2 ^ ℵ₀ := by
    have := Cardinal.lift_le.{u}.2 (h1.trans h2.le)
    simpa using this
  exact h3.trans_lt (hc.isStrongLimit.isStrongPrelimit hc.aleph0_lt)

theorem smallAt_setZF {c : Cardinal.{u}} (hc : c.IsInaccessible) (α : Type) [ContinuumSized α] :
    SmallAt c (setZF.{u} α) := by
  have hlt : (Cardinal.lift.{u} #α).ord < c.ord :=
    Cardinal.ord_lt_ord.2 (lift_mk_lt_of_continuumSized hc α)
  refine smallAt_of_subset (y := ZFSet.vonNeumann (Cardinal.lift.{u} #α).ord) ?_ ?_
  · intro x hx
    obtain ⟨a, rfl⟩ := ZFSet.mem_range.1 hx
    exact ZFSet.mem_vonNeumann.2 (rank_encZF_lt a)
  · rw [smallAt_iff_rank_lt, ZFSet.rank_vonNeumann]
    exact hlt

/-- **A universe tower from a sequence of inaccessible cardinals.** -/
noncomputable def universeTower (κ : ℕ → Cardinal.{u}) (hκ : StrictMono κ)
    (hi : ∀ n, (κ n).IsInaccessible) : UniverseTower.{u} where
  S := ZFSet.{u}
  mem x y := x ∈ y
  ext h := ZFSet.ext h
  lam := depLam
  app := depApp
  app_lam hx := depApp_depLam hx
  lam_ext h := depLam_congr h
  pi := depFuns
  mem_pi := by
    intro A B f
    constructor
    · intro hf
      exact ⟨(depLam_depApp_of_mem hf).symm, fun x hx => depApp_mem (mem_depFuns.1 hf) hx⟩
    · rintro ⟨h1, h2⟩
      rw [h1]
      exact depLam_mem_depFuns h2
  sep A p := ZFSet.sep p A
  mem_sep := ZFSet.mem_sep
  image A f := repl f A
  mem_image := by
    intro A f y
    rw [mem_repl]
    exact ⟨fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩, fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩⟩
  pair := ZFSet.pair
  pair_inj h := ZFSet.pair_injective h
  enc := encZF
  enc_inj h := encZF_injective h
  set := setZF
  mem_set := by
    intro α x
    rw [setZF, ZFSet.mem_range]
    exact ⟨fun ⟨a, e⟩ => ⟨a, e.symm⟩, fun ⟨a, e⟩ => ⟨a, e.symm⟩⟩
  U n := ZFSet.vonNeumann (κ n).ord
  U_mem_U n := by
    rw [ZFSet.mem_vonNeumann, ZFSet.rank_vonNeumann]
    exact Cardinal.ord_lt_ord.2 (hκ n.lt_succ_self)
  U_mono hx := by
    rw [ZFSet.mem_vonNeumann] at hx ⊢
    exact hx.trans (Cardinal.ord_lt_ord.2 (hκ (Nat.lt_succ_self _)))
  U_trans hx hy := smallAt_mem hy hx
  set_mem_U α _ := smallAt_setZF (hi 0) α
  sep_mem_U hA := smallAt_of_subset ZFSet.sep_subset hA
  image_mem_U hA hf := smallAt_repl (hi _) hA hf
  pair_mem_U ha hb := smallAt_orderedPair (hi _) ha hb
  lam_mem_U hA hf := smallAt_depLam (hi _) hA hf
  pi_mem_U hA hB := smallAt_depFuns (hi _) hA hB

/-- `ω` inaccessible cardinals give a universe tower. -/
theorem nonempty_universeTower (h : OmegaInaccessibles.{u}) : Nonempty UniverseTower.{u} := by
  obtain ⟨κ, hκ, hi⟩ := h
  exact ⟨universeTower κ hκ hi⟩

end Lean4LeanModel
