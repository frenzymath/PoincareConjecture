import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.TwoRaySupport

set_option autoImplicit false
open Set Filter
open scoped Topology
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

theorem mesh_support_regular_closed (M : TriangleMesh) :
    closure (interior M.toPlaneComplex.support) = M.toPlaneComplex.support := by
  apply subset_antisymm
    (closure_minimal interior_subset M.toPlaneComplex.isCompact_support.isClosed)
  intro z hz
  rw [M.toPlaneComplex_support] at hz
  obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp hz
  have hsub : M.triangleCarrier t ⊆ M.toPlaneComplex.support := by
    intro w hw
    rw [M.toPlaneComplex_support]
    exact mem_iUnion₂.mpr ⟨t, ht, hw⟩
  apply closure_mono (interior_mono hsub)
  rwa [M.closure_interior_triangleCarrier ⟨t, ht⟩]

theorem first_affine_ray_eq_coordinate_axis (c : AffineBasis (Fin 3) ℝ Plane) :
    (fun t : ℝ => c 0 + t • (c 1 - c 0)) '' Ici (0 : ℝ) =
      {z | 0 ≤ c.coord 1 z ∧ c.coord 2 z = 0} := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    have he : c 0 + t • (c 1 - c 0) = AffineMap.lineMap (c 0) (c 1) t := by
      rw [AffineMap.lineMap_apply]
      change _ = t • (c 1 - c 0) + c 0
      exact add_comm _ _
    simpa [he, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring] using ht
  · rintro ⟨h1, h2⟩
    refine ⟨c.coord 1 z, h1, ?_⟩
    have h := affineBasis_coordinate_reconstruction c z
    simpa only [h2, zero_smul, add_zero] using h

theorem second_affine_ray_eq_coordinate_axis (c : AffineBasis (Fin 3) ℝ Plane) :
    (fun t : ℝ => c 0 + t • (c 2 - c 0)) '' Ici (0 : ℝ) =
      {z | c.coord 1 z = 0 ∧ 0 ≤ c.coord 2 z} := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    have he : c 0 + t • (c 2 - c 0) = AffineMap.lineMap (c 0) (c 2) t := by
      rw [AffineMap.lineMap_apply]
      change _ = t • (c 2 - c 0) + c 0
      exact add_comm _ _
    simpa [he, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring] using ht
  · rintro ⟨h1, h2⟩
    refine ⟨c.coord 2 z, h2, ?_⟩
    have h := affineBasis_coordinate_reconstruction c z
    simpa only [h1, zero_smul, add_zero] using h

theorem closed_regular_support_germ_of_affine_rays
    (c : AffineBasis (Fin 3) ℝ Plane) {K : Set Plane}
    (hK : IsClosed K) (hregular : closure (interior K) = K)
    (hq : c 0 ∈ frontier K)
    (hfront : frontier K =ᶠ[𝓝 (c 0)]
      (((fun t : ℝ => c 0 + t • (c 1 - c 0)) '' Ici (0 : ℝ)) ∪
        ((fun t : ℝ => c 0 + t • (c 2 - c 0)) '' Ici (0 : ℝ)) : Set Plane)) :
    (K =ᶠ[𝓝 (c 0)] {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z}) ∨
      (K =ᶠ[𝓝 (c 0)] {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0}) := by
  apply closed_regular_support_germ_of_two_rays c hK hregular hq
  rw [first_affine_ray_eq_coordinate_axis, second_affine_ray_eq_coordinate_axis,
    union_comm] at hfront
  exact hfront

theorem mesh_support_germ_of_affine_rays
    (M : TriangleMesh) (c : AffineBasis (Fin 3) ℝ Plane)
    (hfront : frontier M.toPlaneComplex.support =ᶠ[𝓝 (c 0)]
      (((fun t : ℝ => c 0 + t • (c 1 - c 0)) '' Ici (0 : ℝ)) ∪
        ((fun t : ℝ => c 0 + t • (c 2 - c 0)) '' Ici (0 : ℝ)) : Set Plane)) :
    (M.toPlaneComplex.support =ᶠ[𝓝 (c 0)] {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z}) ∨
      (M.toPlaneComplex.support =ᶠ[𝓝 (c 0)] {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0}) := by
  apply closed_regular_support_germ_of_affine_rays c
    M.toPlaneComplex.isCompact_support.isClosed (mesh_support_regular_closed M) _ hfront
  apply (propext_iff.mp hfront.eq_of_nhds).mpr
  exact Or.inl ⟨0, by simp, by simp⟩

theorem closed_regular_support_germ_of_affine_line
    (l : Plane →ᵃ[ℝ] ℝ) (hl : Function.Surjective l) {K : Set Plane} {q : Plane}
    (hK : IsClosed K) (hregular : closure (interior K) = K)
    (hq : q ∈ frontier K)
    (hfront : frontier K =ᶠ[𝓝 q] {z | l z = 0}) :
    (K =ᶠ[𝓝 q] {z | 0 ≤ l z}) ∨ (K =ᶠ[𝓝 q] {z | l z ≤ 0}) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hfront
  let A := Metric.ball q r ∩ {z | 0 < l z}
  let B := Metric.ball q r ∩ {z | l z < 0}
  have hboundary : ∀ z ∈ Metric.ball q r, z ∈ frontier K ↔ z ∉ A ∪ B := by
    intro z hz
    change frontier K z ↔ _
    rw [propext_iff.mp (hball hz)]
    simp only [A, B, mem_ofPred_eq, mem_union, mem_inter_iff, hz, true_and,
      not_or, not_lt]
    exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
  have hpos : closure {z | 0 < l z} = {z | 0 ≤ l z} := by
    change closure (l ⁻¹' Ioi (0 : ℝ)) = l ⁻¹' Ici (0 : ℝ)
    rw [← (l.isOpenMap l.continuous_of_finiteDimensional hl).preimage_closure_eq_closure_preimage
      l.continuous_of_finiteDimensional, closure_Ioi]
  have hneg : closure {z | l z < 0} = {z | l z ≤ 0} := by
    change closure (l ⁻¹' Iio (0 : ℝ)) = l ⁻¹' Iic (0 : ℝ)
    rw [← (l.isOpenMap l.continuous_of_finiteDimensional hl).preimage_closure_eq_closure_preimage
      l.continuous_of_finiteDimensional, closure_Iio]
  have hA : closure A =ᶠ[𝓝 q] {z | 0 ≤ l z} := by
    rw [← hpos]
    apply support_eventuallyEq_closure
    filter_upwards [Metric.ball_mem_nhds q hr] with z hz
    exact propext (and_iff_right hz)
  have hB : closure B =ᶠ[𝓝 q] {z | l z ≤ 0} := by
    rw [← hneg]
    apply support_eventuallyEq_closure
    filter_upwards [Metric.ball_mem_nhds q hr] with z hz
    exact propext (and_iff_right hz)
  rcases closed_regular_support_germ_of_two_regions hK hregular
    Metric.isOpen_ball inter_subset_left inter_subset_left
    ((convex_ball q r).inter ((convex_Ioi (0 : ℝ)).affine_preimage l)).isPreconnected
    ((convex_ball q r).inter ((convex_Iio (0 : ℝ)).affine_preimage l)).isPreconnected
    hboundary (Metric.mem_ball_self hr) hq with h | h
  · exact Or.inl (h.trans hA)
  · exact Or.inr (h.trans hB)

theorem mesh_support_germ_of_affine_line
    (M : TriangleMesh) (l : Plane →ᵃ[ℝ] ℝ) (hl : Function.Surjective l)
    {q : Plane} (hq : l q = 0)
    (hfront : frontier M.toPlaneComplex.support =ᶠ[𝓝 q] {z | l z = 0}) :
    (M.toPlaneComplex.support =ᶠ[𝓝 q] {z | 0 ≤ l z}) ∨
      (M.toPlaneComplex.support =ᶠ[𝓝 q] {z | l z ≤ 0}) := by
  exact closed_regular_support_germ_of_affine_line l hl
    M.toPlaneComplex.isCompact_support.isClosed (mesh_support_regular_closed M)
    ((propext_iff.mp hfront.eq_of_nhds).mpr hq) hfront

end PoincareConjecture.Topology.Surface
