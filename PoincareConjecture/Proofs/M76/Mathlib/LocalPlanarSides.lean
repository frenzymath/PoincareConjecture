import PoincareConjecture.Proofs.M76.Mathlib.LocalComplementarySides
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter
open scoped Topology

variable {X : Type*} [TopologicalSpace X]

theorem Homeomorph.exists_local_complementary_sides
    {A : Set X} {a : X} (e : X ≃ₜ (ℝ × ℝ)) (ha : (e a).2 = 0)
    (hlocal : ∀ᶠ x in 𝓝 a, x ∈ A ↔ (e x).2 = 0) :
    ∃ U L R : Set X, IsOpen U ∧ a ∈ U ∧ IsPreconnected L ∧ IsPreconnected R ∧
      U \ A = L ∪ R ∧ A ∩ U ⊆ closure L ∧ A ∩ U ⊆ closure R := by
  have ht : ∀ᶠ y in 𝓝 (e a), e.symm y ∈ A ↔ y.2 = 0 := by
    have he : Tendsto e.symm (𝓝 (e a)) (𝓝 a) := by
      simpa only [Homeomorph.symm_apply_apply] using e.symm.continuous.tendsto (e a)
    simpa only [Homeomorph.apply_symm_apply] using
      he.eventually hlocal
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ht
  let J := Ioo ((e a).1 - δ) ((e a).1 + δ)
  let U := e ⁻¹' (J ×ˢ Ioo (-δ) δ)
  let L := e ⁻¹' (J ×ˢ Ioo (-δ) 0)
  let R := e ⁻¹' (J ×ˢ Ioo 0 δ)
  have hmodel (x : X) (hx : x ∈ U) : x ∈ A ↔ (e x).2 = 0 := by
    have hmem : e x ∈ Metric.ball (e a) δ := by
      rw [← Prod.eta (e a), ← ball_prod_same, Real.ball_eq_Ioo,
        Real.ball_eq_Ioo, ha, zero_sub, zero_add]
      exact hx
    simpa only [mem_ofPred_eq, Homeomorph.symm_apply_apply] using hball hmem
  have hleft : L ⊆ U := by
    intro x hx
    exact ⟨hx.1, hx.2.1, hx.2.2.trans hδ⟩
  have hright : R ⊆ U := by
    intro x hx
    exact ⟨hx.1, (neg_lt_zero.mpr hδ).trans hx.2.1, hx.2.2⟩
  refine ⟨U, L, R, (isOpen_Ioo.prod isOpen_Ioo).preimage e.continuous, ?_,
    e.isPreconnected_preimage.mpr (isPreconnected_Ioo.prod isPreconnected_Ioo),
    e.isPreconnected_preimage.mpr (isPreconnected_Ioo.prod isPreconnected_Ioo), ?_, ?_, ?_⟩
  · change (e a).1 ∈ J ∧ (e a).2 ∈ Ioo (-δ) δ
    rw [ha]
    exact ⟨⟨sub_lt_self _ hδ, lt_add_of_pos_right _ hδ⟩, neg_lt_zero.mpr hδ, hδ⟩
  · ext x
    constructor
    · rintro ⟨hxU, hxA⟩
      have hne : (e x).2 ≠ 0 := fun h => hxA ((hmodel x hxU).mpr h)
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · exact Or.inl ⟨hxU.1, hxU.2.1, hneg⟩
      · exact Or.inr ⟨hxU.1, hpos, hxU.2.2⟩
    · rintro (hxL | hxR)
      · exact ⟨hleft hxL, fun hxA => hxL.2.2.ne ((hmodel x (hleft hxL)).mp hxA)⟩
      · exact ⟨hright hxR, fun hxA => hxR.2.1.ne' ((hmodel x (hright hxR)).mp hxA)⟩
  · intro x hx
    have heq := (hmodel x hx.2).mp hx.1
    change x ∈ closure (e ⁻¹' (J ×ˢ Ioo (-δ) 0))
    rw [← e.preimage_closure]
    change e x ∈ closure (J ×ˢ Ioo (-δ) 0)
    rw [closure_prod_eq, closure_Ioo (neg_ne_zero.mpr hδ.ne')]
    exact ⟨subset_closure hx.2.1, by rw [heq]; exact ⟨neg_nonpos.mpr hδ.le, le_rfl⟩⟩
  · intro x hx
    have heq := (hmodel x hx.2).mp hx.1
    change x ∈ closure (e ⁻¹' (J ×ˢ Ioo 0 δ))
    rw [← e.preimage_closure]
    change e x ∈ closure (J ×ˢ Ioo 0 δ)
    rw [closure_prod_eq, closure_Ioo hδ.ne]
    exact ⟨subset_closure hx.2.1, by rw [heq]; exact ⟨le_rfl, hδ.le⟩⟩

theorem Set.hasLocalComplementarySides_of_local_line_models {A : Set X}
    (h : ∀ a ∈ A, ∃ e : X ≃ₜ (ℝ × ℝ), (e a).2 = 0 ∧
      ∀ᶠ x in 𝓝 a, x ∈ A ↔ (e x).2 = 0) : A.HasLocalComplementarySides := by
  intro a ha
  obtain ⟨e, he, hlocal⟩ := h a ha
  exact e.exists_local_complementary_sides he hlocal
