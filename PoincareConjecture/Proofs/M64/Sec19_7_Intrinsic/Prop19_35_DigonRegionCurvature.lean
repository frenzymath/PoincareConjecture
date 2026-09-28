import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_DigonFanDefects
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_DigonBoundaryTurning
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcLoop
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionBoundaryEuler
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionDiskEulerActual

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

set_option maxHeartbeats 800000 in

open Classical in

theorem m64Intrinsic_digon_angle_sum_le_curvature
    (N : IntrinsicAnnulus) {U V : Set AnnulusCoordinates}
    (R : M64IntrinsicCoordinateTriangulation (closure U))
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hbase : beta 0 = alpha 0) (hend : beta B = alpha A)
    (hmeet : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      alpha s = beta t → (s = 0 ∧ t = 0) ∨ (s = A ∧ t = B))
    (hgeoA : N.metric.IsGeodesicOn alpha (Icc 0 A))
    (hgeoB : N.metric.IsGeodesicOn beta (Icc 0 B))
    (hunitA : ∀ t ∈ Icc 0 A, N.metric.inner (alpha t) (deriv alpha t) (deriv alpha t) = 1)
    (hunitB : ∀ t ∈ Icc 0 B, N.metric.inner (beta t) (deriv beta t) (deriv beta t) = 1)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B)
    (hfV : frontier V = frontier U)
    (hclosure : closure U ∪ closure V = univ) (hVconn : IsPreconnected V)
    (v0 v1 : Euler.CoordinateVertex R.coordinates R.basis)
    (hv0 : v0.1 = alpha 0) (hv1 : v1.1 = alpha A) :
    coordinateVertexAngleContribution N.metric R.coordinates R.basis v0.1 +
        coordinateVertexAngleContribution N.metric R.coordinates R.basis v1.1 ≤
      ∫ x in closure U, N.connection.scalarCurvature x / 2 ∂N.metric.volumeMeasure := by
  classical
  let _ := Fintype.ofFinite (Euler.CoordinateVertex R.coordinates R.basis)
  let _ : Nonempty (Fin R.count) := by
    obtain ⟨⟨i, _⟩, _⟩ := v0.2
    exact ⟨i⟩
  let Q (i : Fin R.count) := N.metric.alignedChartFrame
    (coordinateTriangleChart (R.coordinates i) (R.basis i))
    (coordinateTriangleChart_smooth _ _ (R.inverse_smooth i))
    (coordinateTriangleChart_smooth_symm _ _ (R.smooth i))
  have hregA (t : ℝ) (ht : t ∈ Ioo 0 A) : deriv alpha t ≠ 0 := by
    intro hz
    have hu := hunitA t (Ioo_subset_Icc_self ht)
    simp only [hz, map_zero] at hu
    norm_num at hu
  have hregB (t : ℝ) (ht : t ∈ Ioo 0 B) : deriv beta t ≠ 0 := by
    intro hz
    have hu := hunitB t (Ioo_subset_Icc_self ht)
    simp only [hz, map_zero] at hu
    norm_num at hu
  obtain ⟨loop, hl, he, hi, himage⟩ :=
    m64Intrinsic_exists_simple_loop_between_arcs hA hB ha.continuous.continuousOn
      hb.continuous.continuousOn hai hbi hbase.symm hend.symm hmeet
  have hloopFrontier : loop '' Icc (0 : ℝ) 2 = frontier U := himage.trans hfront.symm
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
  have hdefect := m64Intrinsic_digon_fan_defects R N.metric ha hb hA hai hbi hregA hregB
    hbase hend hmeet hU hV hUV hfront hfV v0 v1 hv0 hv1
  have hturn := m64Intrinsic_digon_boundary_turning_eq_zero N R Q ha hb hai hbi
    hgeoA hgeoB hunitA hunitB hmeet hU hV hUV hfront hfV v0 v1 hv0 hv1
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
    coordinateVertexAngleContribution N.metric R.coordinates R.basis v0.1 -
    coordinateVertexAngleContribution N.metric R.coordinates R.basis v1.1 at hdefect
  change turning = 0 at hturn
  rw [integral_div]
  change _ + _ ≤ curvature / 2
  linarith only [htotal', hdefect, hturn]

end PoincareConjecture
