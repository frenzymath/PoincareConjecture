import PoincareConjecture.Proofs.M76.Mathlib.CollarCutMembership
import Mathlib.Topology.Algebra.Field











set_option autoImplicit false

open Set

namespace Homeomorph

variable {E : Type*} [TopologicalSpace E]





theorem positive_collar_image_isPreconnected
    {B T s : Set E} {upper : E → ℝ}
    (C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T)
    (hs : IsPreconnected s) (hsB : s ⊆ B) (hu : ContinuousOn upper s)
    (hpos : ∀ x ∈ s, 0 < upper x) :
    IsPreconnected ((fun p => (C p : E)) ''
      {p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} |
        (p : E × ℝ).1 ∈ s ∧ 0 < (p : E × ℝ).2}) := by
  let I := Ioc (0 : ℝ) 1
  let P : s × I → {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} :=
    fun z => ⟨((z.1 : E), (z.2 : ℝ) * upper z.1), hsB z.1.property,
      (mul_pos z.2.property.1 (hpos z.1 z.1.property)).le,
      mul_le_of_le_one_left (hpos z.1 z.1.property).le z.2.property.2⟩
  have huc : Continuous (fun x : s => upper x) :=
    continuousOn_iff_continuous_domRestrict.mp hu
  have hP : Continuous P :=
    ((continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp continuous_snd).mul (huc.comp continuous_fst))).subtype_mk _
  let f : s × I → E := fun z => C (P z)
  have hf : Continuous f := continuous_subtype_val.comp (C.continuous.comp hP)
  let : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs
  let : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioc
  have himage : range f = (fun p => (C p : E)) ''
      {p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} |
        (p : E × ℝ).1 ∈ s ∧ 0 < (p : E × ℝ).2} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨P z, ⟨z.1.property, mul_pos z.2.property.1 (hpos z.1 z.1.property)⟩, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      let x : s := ⟨(p : E × ℝ).1, hp.1⟩
      let z : I := ⟨(p : E × ℝ).2 / upper x,
        div_pos hp.2 (hpos x x.property), (div_le_one (hpos x x.property)).mpr p.property.2.2⟩
      refine ⟨(x, z), ?_⟩
      apply congrArg (fun p => (C p : E))
      apply Subtype.ext
      exact Prod.ext rfl (div_mul_cancel₀ _ (hpos x x.property).ne')
  rw [← himage]
  exact isPreconnected_range hf





theorem positive_collar_subset_cut_side
    {B T s s₀ s₁ : Set E} {upper A : E → ℝ}
    (C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hs : IsPreconnected s) (hsB : s ⊆ B) (hu : ContinuousOn upper s)
    (hpos : ∀ x ∈ s, 0 < upper x) (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁)
    (hcover : T ⊆ s₀ ∪ s₁) (hzero : s₀ ∩ s₁ ⊆ {x | A x = 0}) :
    (∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).1 ∈ s → 0 < (p : E × ℝ).2 → (C p : E) ∈ s₀ \ s₁) ∨
    (∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).1 ∈ s → 0 < (p : E × ℝ).2 → (C p : E) ∈ s₁ \ s₀) := by
  let S := (fun p => (C p : E)) ''
    {p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} |
      (p : E × ℝ).1 ∈ s ∧ 0 < (p : E × ℝ).2}
  have hS : IsPreconnected S := C.positive_collar_image_isPreconnected hs hsB hu hpos
  have hSc : S ⊆ s₀ ∪ s₁ := by
    rintro y ⟨p, _, rfl⟩
    exact hcover (C p).property
  have hSn : S ∩ (s₀ ∩ s₁) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨⟨p, hp, rfl⟩, hy⟩
    exact hp.2.ne' ((hheight p).symm.trans (hzero hy))
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hS s₀ s₁ hs₀ hs₁ hSc hSn
    with h | h
  · left
    intro p hp ht
    have hm : (C p : E) ∈ S := ⟨p, ⟨hp, ht⟩, rfl⟩
    exact ⟨h hm, fun hy => (hSn.subset ⟨hm, h hm, hy⟩).elim⟩
  · right
    intro p hp ht
    have hm : (C p : E) ∈ S := ⟨p, ⟨hp, ht⟩, rfl⟩
    exact ⟨h hm, fun hy => (hSn.subset ⟨hm, hy, h hm⟩).elim⟩

end Homeomorph
