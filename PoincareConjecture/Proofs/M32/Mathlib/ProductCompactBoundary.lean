import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Tactic.Linarith










set_option autoImplicit false

open Set
open scoped Topology

universe u v

namespace PoincareConjecture.M32




theorem isCompact_subset_fiber_of_frontier_subset
    {X : Type u} [TopologicalSpace X] {K : Set (X × ℝ)} (hK : IsCompact K)
    {a : ℝ} (hfront : frontier K ⊆ {z | z.2 = a}) : K ⊆ {z | z.2 = a} := by
  intro z hz
  obtain ⟨lo, hlo, hmin⟩ := hK.exists_isMinOn ⟨z, hz⟩ continuous_snd.continuousOn
  obtain ⟨hi, hhi, hmax⟩ := hK.exists_isMaxOn ⟨z, hz⟩ continuous_snd.continuousOn
  have hlofront : lo ∈ frontier K := by
    refine ⟨subset_closure hlo, ?_⟩
    intro hint
    have hnh : (fun r : ℝ => (lo.1, r)) ⁻¹' interior K ∈ 𝓝 lo.2 :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
        (isOpen_interior.mem_nhds hint)
    obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hnh
    have hmem : (lo.1, lo.2 - delta / 2) ∈ K := interior_subset (hball (by
      change |lo.2 - delta / 2 - lo.2| < delta
      exact abs_lt.mpr ⟨by linarith, by linarith⟩))
    have hle := hmin hmem
    change lo.2 ≤ lo.2 - delta / 2 at hle
    linarith
  have hhifront : hi ∈ frontier K := by
    refine ⟨subset_closure hhi, ?_⟩
    intro hint
    have hnh : (fun r : ℝ => (hi.1, r)) ⁻¹' interior K ∈ 𝓝 hi.2 :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
        (isOpen_interior.mem_nhds hint)
    obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hnh
    have hmem : (hi.1, hi.2 + delta / 2) ∈ K := interior_subset (hball (by
      change |hi.2 + delta / 2 - hi.2| < delta
      exact abs_lt.mpr ⟨by linarith, by linarith⟩))
    have hle := hmax hmem
    change hi.2 + delta / 2 ≤ hi.2 at hle
    linarith
  have hloe : lo.2 = a := hfront hlofront
  have hhie : hi.2 = a := hfront hhifront
  have hlow := hmin hz
  have hupp := hmax hz
  change lo.2 ≤ z.2 at hlow
  change z.2 ≤ hi.2 at hupp
  change z.2 = a
  linarith




theorem not_isCompact_of_product_chart_frontier
    {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
    {U K : Set M} (hU : IsOpen U) (hKU : K ⊆ U) (e : U ≃ₜ X × ℝ)
    {a : ℝ} (hint : (interior K).Nonempty)
    (hfront : e '' ((Subtype.val : U → M) ⁻¹' frontier K) ⊆ {z | z.2 = a}) :
    ¬ IsCompact K := by
  intro hK
  have hrange : K ⊆ range (Subtype.val : U → M) := by
    intro x hx
    exact ⟨⟨x, hKU hx⟩, rfl⟩
  have hcompact := Topology.IsInducing.subtypeVal.isCompact_preimage' hK hrange
  have hfront' : frontier (e '' ((Subtype.val : U → M) ⁻¹' K)) ⊆
      {z | z.2 = a} := by
    rw [← e.image_frontier,
      ← hU.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
        continuous_subtype_val K]
    exact hfront
  have hsub := isCompact_subset_fiber_of_frontier_subset
    (hcompact.image e.continuous) hfront'
  obtain ⟨x, hx⟩ := hint
  let xU : U := ⟨x, hKU (interior_subset hx)⟩
  have hopen : IsOpen (e '' ((Subtype.val : U → M) ⁻¹' interior K)) :=
    e.isOpenMap _ (isOpen_interior.preimage continuous_subtype_val)
  have hpoint : e xU ∈ e '' ((Subtype.val : U → M) ⁻¹' interior K) :=
    ⟨xU, hx, rfl⟩
  have hnh : (fun r : ℝ => ((e xU).1, r)) ⁻¹'
      (e '' ((Subtype.val : U → M) ⁻¹' interior K)) ∈ 𝓝 (e xU).2 :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hopen.mem_nhds hpoint)
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hnh
  have hmem : ((e xU).1, (e xU).2 + delta / 2) ∈
      e '' ((Subtype.val : U → M) ⁻¹' interior K) := hball (by
    change |(e xU).2 + delta / 2 - (e xU).2| < delta
    exact abs_lt.mpr ⟨by linarith, by linarith⟩)
  have heq : (e xU).2 = a := hsub
    (show e xU ∈ e '' ((Subtype.val : U → M) ⁻¹' K) from
      ⟨xU, show x ∈ K from interior_subset hx, rfl⟩)
  have heq' := hsub (image_mono (preimage_mono interior_subset) hmem)
  change (e xU).2 + delta / 2 = a at heq'
  linarith

end PoincareConjecture.M32
