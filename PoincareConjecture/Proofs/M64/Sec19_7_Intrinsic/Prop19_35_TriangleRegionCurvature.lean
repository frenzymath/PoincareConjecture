import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleFanDefects
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcLoop
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionBoundaryEuler
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionDiskEulerActual

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

set_option maxHeartbeats 800000 in

open Classical in

theorem m64Intrinsic_triangle_region_angle_le_curvature_turning
    (N : IntrinsicAnnulus) {U V : Set AnnulusCoordinates}
    (R : M64IntrinsicCoordinateTriangulation (closure U))
    (Q : ∀ i, RiemannianMetric.AlignedChartFrame N.metric
      (coordinateTriangleChart (R.coordinates i) (R.basis i)))
    {base alpha beta : ℝ → AnnulusCoordinates} {D A B : ℝ}
    (hc : ContDiff ℝ ∞ base) (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    (hD : 0 < D) (hA : 0 < A) (hB : 0 < B)
    (hci : InjOn base (Icc 0 D)) (hai : InjOn alpha (Icc 0 A))
    (hbi : InjOn beta (Icc 0 B))
    (hcreg : ∀ t ∈ Ioo 0 D, deriv base t ≠ 0)
    (hareg : ∀ t ∈ Ioo 0 A, deriv alpha t ≠ 0)
    (hbreg : ∀ t ∈ Ioo 0 B, deriv beta t ≠ 0)
    (hstartA : base 0 = alpha 0) (hstartB : base D = beta 0)
    (hmeet : alpha A = beta B)
    (hbaseA : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 A, base s = alpha t → s = 0 ∧ t = 0)
    (hbaseB : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 B, base s = beta t → s = D ∧ t = 0)
    (hsides : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B, alpha s = beta t → s = A ∧ t = B)
    (hreg0 : deriv base 0 ≠ 0) (hreg1 : deriv base D ≠ 0)
    (horth0 : N.metric.inner (base 0) (deriv base 0) (deriv alpha 0) = 0)
    (horth1 : N.metric.inner (base D) (deriv base D) (deriv beta 0) = 0)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (hfV : frontier V = frontier U)
    (hclosure : closure U ∪ closure V = univ) (hVconn : IsPreconnected V)
    (hnorm0 : ‖base 0‖ = 1) (hnorm1 : ‖base D‖ = 1)
    (hinward0 : 0 < inner ℝ (base 0) (deriv alpha 0))
    (hinward1 : 0 < inner ℝ (base D) (deriv beta 0))
    (hsub : closure U ⊆ standardAnnulusDomain)
    (v0 v1 vT : Euler.CoordinateVertex R.coordinates R.basis)
    (hv0 : v0.1 = base 0) (hv1 : v1.1 = base D) (hvT : vT.1 = alpha A) :
    coordinateVertexAngleContribution N.metric R.coordinates R.basis vT.1 ≤
      (∫ x in closure U, N.connection.scalarCurvature x / 2 ∂N.metric.volumeMeasure) +
        ∑ p : Fin R.count × Fin 3, if ∀ q : Fin R.count × Fin 3,
            faceBoundaryIndex R.face q.1 q.2 = faceBoundaryIndex R.face p.1 p.2 → q = p then
          coordinateTriangleTurningIntegral N.connection (R.coordinates p.1) (R.basis p.1)
            (Q p.1) (p.2 + 1) ((p.2 + 1) + 1) else 0 := by
  classical
  let _ := Fintype.ofFinite (Euler.CoordinateVertex R.coordinates R.basis)
  let _ : Nonempty (Fin R.count) := by
    obtain ⟨⟨i, _⟩, _⟩ := v0.2
    exact ⟨i⟩
  let gamma (e : Bool) := if e then beta else base
  let T (e : Bool) := if e then B else D
  have hg (e : Bool) : ContinuousOn (gamma e) (Icc 0 (T e)) := by
    cases e
    · exact hc.continuous.continuousOn
    · exact hb.continuous.continuousOn
  have hT (e : Bool) : 0 < T e := by
    cases e
    · exact hD
    · exact hB
  have hgi (e : Bool) : InjOn (gamma e) (Icc 0 (T e)) := by
    cases e
    · exact hci
    · exact hbi
  have hba : ∀ s ∈ Icc 0 B, ∀ t ∈ Icc 0 A, beta s = alpha t → s = B ∧ t = A := by
    intro s hs t ht he
    exact (hsides t ht s hs he.symm).symm
  obtain ⟨loop, hl, he, hi, himage⟩ := m64Intrinsic_exists_three_arc_loop gamma alpha T
    hg ha.continuous.continuousOn hT hA hgi hai hstartA.symm hmeet hstartB
    hbaseB hbaseA hba
  change loop '' Icc (0 : ℝ) 2 = base '' Icc 0 D ∪ beta '' Icc 0 B ∪
    alpha '' Icc 0 A at himage
  have hloopFrontier : loop '' Icc (0 : ℝ) 2 = frontier U :=
    himage.trans (hfront.trans (by ac_rfl)).symm
  have htrace : frontier (⋃ i, (R.face i).carrier) = loop '' Icc (0 : ℝ) 2 := by
    rw [R.cover, (m64Intrinsic_jordan_interior_closure hU hV hUV hfV.symm).2, hloopFrontier]
  have hgb := m64Intrinsic_region_gaussBonnet_boundary_defects R.face R.coordinates R.basis
    R.smooth R.inverse_smooth R.source R.carrier R.boundary R.intersections
    R.intersection_frontier (by norm_num : (0 : ℝ) < 2) hl he hi htrace N.connection Q
  have hcoefficient (v : Euler.CoordinateVertex R.coordinates R.basis) :
      (if v.1 ∈ loop '' Icc (0 : ℝ) 2 then Real.pi else 2 * Real.pi) =
        (if v.1 ∈ frontier U then Real.pi else 2 * Real.pi) := by
    by_cases hv : v.1 ∈ frontier U
    · have hvl : v.1 ∈ loop '' Icc (0 : ℝ) 2 := by rwa [hloopFrontier]
      simp only [if_pos hv, if_pos hvl]
    · have hvl : v.1 ∉ loop '' Icc (0 : ℝ) 2 := by rwa [hloopFrontier]
      simp only [if_neg hv, if_neg hvl]
  simp_rw [hcoefficient] at hgb
  rw [R.cover] at hgb
  have hdefect := m64Intrinsic_triangle_region_fan_defects R N.metric hc ha hb hD hA hB
    hci hai hbi hcreg hareg hbreg hstartA hstartB hmeet hbaseA hbaseB hsides hreg0 hreg1
    horth0 horth1 hU hV hUV hfront hfV hnorm0 hnorm1 hinward0 hinward1 hsub
    v0 v1 vT hv0 hv1 hvT
  have heuler := m64Intrinsic_region_euler_ge_one_of_coordinate_triangulation
    R.face R.coordinates R.basis R.source R.carrier R.boundary R.intersection_frontier
    R.intersections hU hV hUV hfV.symm hclosure R.cover hVconn
  have heulerR : (1 : ℝ) ≤ (Nat.card (Euler.CoordinateVertex R.coordinates R.basis) : ℝ) -
      Nat.card (FaceBoundaryEdge R.face) + Nat.card (Fin R.count) := by exact_mod_cast heuler
  have heulerPi := mul_le_mul_of_nonneg_left heulerR
    (show 0 ≤ 4 * Real.pi by positivity)
  dsimp only at hgb hdefect
  have htotal := heulerPi.trans_eq hgb.symm
  let curvature := ∫ x in closure U, N.connection.scalarCurvature x ∂N.metric.volumeMeasure
  let turning := ∑ p : Fin R.count × Fin 3, if ∀ q : Fin R.count × Fin 3,
      faceBoundaryIndex R.face q.1 q.2 = faceBoundaryIndex R.face p.1 p.2 → q = p then
    coordinateTriangleTurningIntegral N.connection (R.coordinates p.1) (R.basis p.1)
      (Q p.1) (p.2 + 1) ((p.2 + 1) + 1) else 0
  let defects := ∑ v : Euler.CoordinateVertex R.coordinates R.basis,
    ((if v.1 ∈ frontier U then Real.pi else 2 * Real.pi) -
      coordinateVertexAngleContribution N.metric R.coordinates R.basis v.1)
  have htotal' : 4 * Real.pi * 1 ≤ curvature + 2 * turning + 2 * defects := by
    convert htotal using 1
    · rfl
    · congr 2
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> rfl
  change defects = 2 * Real.pi -
    coordinateVertexAngleContribution N.metric R.coordinates R.basis vT.1 at hdefect
  rw [integral_div]
  change coordinateVertexAngleContribution N.metric R.coordinates R.basis vT.1 ≤
    curvature / 2 + turning
  linarith only [htotal', hdefect]

end PoincareConjecture
