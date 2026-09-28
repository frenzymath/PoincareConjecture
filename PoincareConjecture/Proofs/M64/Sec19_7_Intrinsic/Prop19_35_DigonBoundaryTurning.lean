import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_DigonTriangulation
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcStraightFan
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcSideClassification
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GeodesicArcSideTurning

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

open Classical in

theorem m64Intrinsic_digon_boundary_turning_eq_zero
    (N : IntrinsicAnnulus) {U V : Set AnnulusCoordinates}
    (R : M64IntrinsicCoordinateTriangulation (closure U))
    (Q : ∀ i, RiemannianMetric.AlignedChartFrame N.metric
      (coordinateTriangleChart (R.coordinates i) (R.basis i)))
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ}
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hgeoA : N.metric.IsGeodesicOn alpha (Icc 0 A))
    (hgeoB : N.metric.IsGeodesicOn beta (Icc 0 B))
    (hunitA : ∀ t ∈ Icc 0 A, N.metric.inner (alpha t) (deriv alpha t) (deriv alpha t) = 1)
    (hunitB : ∀ t ∈ Icc 0 B, N.metric.inner (beta t) (deriv beta t) (deriv beta t) = 1)
    (hmeet : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      alpha s = beta t → (s = 0 ∧ t = 0) ∨ (s = A ∧ t = B))
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B)
    (hfV : frontier V = frontier U)
    (v0 v1 : Euler.CoordinateVertex R.coordinates R.basis)
    (hv0 : v0.1 = alpha 0) (hv1 : v1.1 = alpha A) :
    (∑ p : Fin R.count × Fin 3, if ∀ q : Fin R.count × Fin 3,
        faceBoundaryIndex R.face q.1 q.2 = faceBoundaryIndex R.face p.1 p.2 → q = p then
      coordinateTriangleTurningIntegral N.connection (R.coordinates p.1) (R.basis p.1)
        (Q p.1) (p.2 + 1) ((p.2 + 1) + 1) else 0) = 0 := by
  have htrace : frontier (⋃ i, (R.face i).carrier) = frontier U := by
    rw [R.cover, (m64Intrinsic_jordan_interior_closure hU hV hUV hfV.symm).2]
  have hAB : alpha '' Icc 0 A ∩ beta '' Icc 0 B ⊆ {v0.1, v1.1} := by
    rintro z ⟨⟨s, hs, hsz⟩, ⟨t, ht, htz⟩⟩
    rcases hmeet s hs t ht (hsz.trans htz.symm) with h | h
    · exact Or.inl (hsz.symm.trans ((congrArg alpha h.1).trans hv0.symm))
    · exact Or.inr (hsz.symm.trans ((congrArg alpha h.1).trans hv1.symm))
  apply Finset.sum_eq_zero
  intro p _
  split_ifs with hp
  · have himage : ((R.face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆
        alpha '' Icc 0 A ∪ beta '' Icc 0 B := by
      rw [← hfront, ← htrace]
      exact m64Intrinsic_unpaired_side_subset_region_frontier R.face R.coordinates R.basis
        R.source R.boundary R.intersections p hp
    have hclass := m64Intrinsic_unpaired_side_subset_one_of_two_arcs
      R.face R.coordinates R.basis R.source R.carrier R.boundary R.intersections p hp
      (isCompact_Icc.image ha.continuous).isClosed
      (isCompact_Icc.image hb.continuous).isClosed himage v0 v1 hAB
    have hcyclic : (fun t : ℝ => R.coordinates p.1
        (AffineMap.lineMap (R.basis p.1 (p.2 + 1))
          (R.basis p.1 ((p.2 + 1) + 1)) t)) '' Icc (0 : ℝ) 1 =
        ((R.face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 := by
      rw [coordinateTriangle_cyclic_boundary_image, R.boundary, image_comp]
      congr 1
      unfold affineSegment
      apply image_congr
      intro t _
      simp only [affineChartSegment, AffineMap.lineMap_apply_module]
      module
    have hne : p.2 + 1 ≠ (p.2 + 1) + 1 := by
      have h (k : Fin 3) : k + 1 ≠ (k + 1) + 1 := by fin_cases k <;> decide
      exact h p.2
    rcases hclass with hac | hbc
    · apply m64Intrinsic_coordinate_side_geodesic_arc_turning_eq_zero N.connection
        (R.coordinates p.1) (R.basis p.1) (R.smooth p.1) (R.inverse_smooth p.1)
        (R.source p.1) (Q p.1) hne ha hgeoA hai hunitA
      rwa [hcyclic]
    · apply m64Intrinsic_coordinate_side_geodesic_arc_turning_eq_zero N.connection
        (R.coordinates p.1) (R.basis p.1) (R.smooth p.1) (R.inverse_smooth p.1)
        (R.source p.1) (Q p.1) hne hb hgeoB hbi hunitB
      rwa [hcyclic]
  · rfl

end PoincareConjecture
