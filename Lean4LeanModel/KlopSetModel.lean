import Lean4LeanModel.DependentFunction
import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.SetModel

/-!
# `ZFSet` is a set model

`zfSetModel`: `ZFSet` is a `Lean4Lean.VEnv.Strengthening.SetModel`, with functions as graphs and
the types of the lowest universe encoded by initial segments of a well-order. No hypothesis on
cardinals is used.
-/

namespace Lean4LeanModel

open Cardinal Ordinal Lean4Lean Lean4Lean.VEnv.Strengthening

universe u

/-- A well-order of `α` of order type the initial ordinal of its cardinality. -/
noncomputable def encRel (α : Type) : α → α → Prop := (Cardinal.exists_ord_eq α).choose

instance (α : Type) : IsWellOrder α (encRel α) := (Cardinal.exists_ord_eq α).choose_spec.choose

/-- The encoding of an element of a type of the lowest universe: the von Neumann ordinal of its
position in `encRel`. -/
noncomputable def encZF {α : Type} (a : α) : ZFSet.{u} :=
  (Ordinal.lift.{u} (typein (encRel α) a)).toZFSet

theorem encZF_injective {α : Type} : Function.Injective (encZF.{u} (α := α)) := by
  intro a b h
  have := Ordinal.lift_inj.1 (toZFSet_injective h)
  exact (typein_injective (encRel α)) this

/-- The set of encodings of the elements of `α`. -/
noncomputable def setZF (α : Type) : ZFSet.{u} := ZFSet.range (encZF.{u} (α := α))

/-- **`ZFSet` is a set model.** -/
noncomputable def zfSetModel : SetModel.{u} where
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
  sUnion := ZFSet.sUnion
  mem_sUnion := by
    intro A x
    exact ZFSet.mem_sUnion.trans
      ⟨fun ⟨y, hy, hx⟩ => ⟨y, hy, hx⟩, fun ⟨y, hy, hx⟩ => ⟨y, hy, hx⟩⟩

end Lean4LeanModel
