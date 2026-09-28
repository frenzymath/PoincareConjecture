import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JordanCorner

noncomputable section
set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace PoincareConjecture

theorem m64Intrinsic_regular_support_product_line_germ
    {K : Set (ℝ × ℝ)} (hK : IsClosed K) (hregular : closure (interior K) = K)
    {x : ℝ} (hp : (x, 0) ∈ frontier K)
    (hfront : ∀ᶠ z in 𝓝 (x, (0 : ℝ)), z ∈ frontier K ↔ z.2 = 0) :
    (∀ᶠ z in 𝓝 (x, (0 : ℝ)), z ∈ K ↔ 0 ≤ z.2) ∨
      (∀ᶠ z in 𝓝 (x, (0 : ℝ)), z ∈ K ↔ z.2 ≤ 0) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hfront
  let W := ball (x, (0 : ℝ)) r
  let A := W ∩ ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ))
  let B := W ∩ ((univ : Set ℝ) ×ˢ Iio (0 : ℝ))
  have hA : IsPreconnected A :=
    ((convex_ball _ _).inter (convex_univ.prod (convex_Ioi (0 : ℝ)))).isPreconnected
  have hB : IsPreconnected B :=
    ((convex_ball _ _).inter (convex_univ.prod (convex_Iio (0 : ℝ)))).isPreconnected
  have hboundary : ∀ z ∈ W, z ∈ frontier K ↔ z ∉ A ∪ B := by
    intro z hz
    have hfrontz : z ∈ frontier K ↔ z.2 = 0 := hball hz
    rw [hfrontz]
    simp only [A, B, mem_union, mem_inter_iff, mem_prod, mem_univ, mem_Ioi,
      mem_Iio, hz, true_and, not_or, not_lt]
    exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
  have hAcl : closure A =ᶠ[𝓝 (x, (0 : ℝ))] {z : ℝ × ℝ | 0 ≤ z.2} := by
    have h := Topology.Surface.support_eventuallyEq_closure
      (A := A) (B := (univ : Set ℝ) ×ˢ Ioi (0 : ℝ)) (q := (x, (0 : ℝ))) (by
        filter_upwards [Metric.ball_mem_nhds (x, (0 : ℝ)) hr] with z hz
        exact propext (and_iff_right hz))
    rw [closure_prod_eq, closure_univ, closure_Ioi] at h
    have heq : ((univ : Set ℝ) ×ˢ Ici (0 : ℝ)) = {z : ℝ × ℝ | 0 ≤ z.2} := by
      ext z
      simp
    rwa [heq] at h
  have hBcl : closure B =ᶠ[𝓝 (x, (0 : ℝ))] {z : ℝ × ℝ | z.2 ≤ 0} := by
    have h := Topology.Surface.support_eventuallyEq_closure
      (A := B) (B := (univ : Set ℝ) ×ˢ Iio (0 : ℝ)) (q := (x, (0 : ℝ))) (by
        filter_upwards [Metric.ball_mem_nhds (x, (0 : ℝ)) hr] with z hz
        exact propext (and_iff_right hz))
    rw [closure_prod_eq, closure_univ, closure_Iio] at h
    have heq : ((univ : Set ℝ) ×ˢ Iic (0 : ℝ)) = {z : ℝ × ℝ | z.2 ≤ 0} := by
      ext z
      simp
    rwa [heq] at h
  rcases Topology.Surface.closed_regular_support_germ_of_two_regions hK hregular
    isOpen_ball (show A ⊆ W from inter_subset_left) (show B ⊆ W from inter_subset_left)
      hA hB hboundary (mem_ball_self hr) hp with h | h
  · left
    filter_upwards [h.trans hAcl] with z hz
    exact propext_iff.mp hz
  · right
    filter_upwards [h.trans hBcl] with z hz
    exact propext_iff.mp hz

theorem m64Intrinsic_jordan_product_line_germ
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfront : frontier U = frontier V)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {x : ℝ}
    (hx : (x, 0) ∈ H.source) (hp : H (x, 0) ∈ frontier U)
    (hline : ∀ᶠ z in 𝓝 (x, (0 : ℝ)), H z ∈ frontier U ↔ z.2 = 0) :
    (∀ᶠ z in 𝓝 (x, (0 : ℝ)), H z ∈ closure U ↔ 0 ≤ z.2) ∨
      (∀ᶠ z in 𝓝 (x, (0 : ℝ)), H z ∈ closure U ↔ z.2 ≤ 0) := by
  let S := H.source ∩ H ⁻¹' U
  let K := closure S
  have hS : IsOpen S := H.isOpen_inter_preimage hU
  have himage : H.IsImage S U := by
    intro z hz
    exact ⟨fun hu => ⟨hz, hu⟩, fun hu => hu.2⟩
  have hregular : closure (interior K) = K := by
    apply Subset.antisymm isClosed_closure.closure_interior_subset
    exact closure_mono hS.subset_interior_closure
  have hfcl := (m64Intrinsic_jordan_interior_closure hU hV hdisj hfront).2
  have hKfront : (x, 0) ∈ frontier K := by
    apply (himage.closure.frontier hx).mp
    rwa [hfcl]
  have hlineK : ∀ᶠ z in 𝓝 (x, (0 : ℝ)), z ∈ frontier K ↔ z.2 = 0 := by
    filter_upwards [H.open_source.mem_nhds hx, hline] with z hz hlin
    rw [← himage.closure.frontier hz, hfcl]
    exact hlin
  rcases m64Intrinsic_regular_support_product_line_germ isClosed_closure hregular
    hKfront hlineK with h | h
  · left
    filter_upwards [H.open_source.mem_nhds hx, h] with z hz heq
    exact (himage.closure hz).trans heq
  · right
    filter_upwards [H.open_source.mem_nhds hx, h] with z hz heq
    exact (himage.closure hz).trans heq

end PoincareConjecture
