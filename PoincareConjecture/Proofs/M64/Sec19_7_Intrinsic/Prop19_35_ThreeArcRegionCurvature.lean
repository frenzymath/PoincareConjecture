import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcLoop
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcFanDefects
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




theorem m64Intrinsic_three_arc_region_curvature_turning_ge_pi_div_two
    (N : IntrinsicAnnulus) {U V : Set AnnulusCoordinates}
    (R : M64IntrinsicCoordinateTriangulation (closure U))
    (Q : ∀ i, RiemannianMetric.AlignedChartFrame N.metric
      (coordinateTriangleChart (R.coordinates i) (R.basis i)))
    (gamma : Bool → ℝ → AnnulusCoordinates) (sigma : ℝ → AnnulusCoordinates)
    (T : Bool → ℝ) {S speed : ℝ} (hg : ∀ e, ContDiff ℝ ∞ (gamma e))
    (hs : ContDiff ℝ ∞ sigma) (hT : ∀ e, 0 < T e) (hS : 0 < S) (hspeed : 0 < speed)
    (hinj : ∀ e, InjOn (gamma e) (Icc 0 (T e))) (hsi : InjOn sigma (Icc 0 S))
    (hstart : sigma 0 = gamma false 0) (hend : sigma S = gamma true (T true))
    (hjoin : gamma false (T false) = gamma true 0)
    (hreg : deriv (gamma false) (T false) ≠ 0)
    (htan : deriv (gamma true) 0 = speed • deriv (gamma false) (T false))
    (hab : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 (T true),
      gamma false x = gamma true y → x = T false ∧ y = 0)
    (has : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 S,
      gamma false x = sigma y → x = 0 ∧ y = 0)
    (hbs : ∀ x ∈ Icc 0 (T true), ∀ y ∈ Icc 0 S,
      gamma true x = sigma y → x = T true ∧ y = S)
    (hregular : ∀ e, ∀ t ∈ Ioo (0 : ℝ) (T e), deriv (gamma e) t ≠ 0)
    (hsreg : ∀ t ∈ Ioo (0 : ℝ) S, deriv sigma t ≠ 0)
    (hreg0 : deriv (gamma false) 0 ≠ 0)
    (horth : N.metric.inner (gamma false 0) (deriv (gamma false) 0) (deriv sigma 0) = 0)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfU : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S)
    (hfV : frontier V = frontier U)
    (hclosure : closure U ∪ closure V = univ) (hVconn : IsPreconnected V)
    (hnorm : ‖gamma false 0‖ = 1)
    (hinward : 0 < inner ℝ (gamma false 0) (deriv sigma 0))
    (hsub : closure U ⊆ standardAnnulusDomain)
    (v0 v1 : Euler.CoordinateVertex R.coordinates R.basis)
    (hv0 : v0.1 = gamma false 0) (hv1 : v1.1 = gamma true (T true)) :
    Real.pi / 2 ≤
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
  obtain ⟨loop, hl, he, hi, himage⟩ := m64Intrinsic_exists_three_arc_loop gamma sigma T
    (fun e => (hg e).continuous.continuousOn) hs.continuous.continuousOn hT hS
    hinj hsi hstart hend hjoin hab has hbs
  have hloopFrontier : loop '' Icc (0 : ℝ) 2 = frontier U := himage.trans hfU.symm
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
  have hdefect := m64Intrinsic_three_arc_region_fan_defects_le R N.metric gamma sigma T
    hg hs hT hS hspeed hinj hsi hstart hend hjoin hreg htan hab has hbs hregular hsreg
    hreg0 horth hU hV hUV hfU hfV hnorm hinward hsub v0 v1 hv0 hv1
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
  change defects ≤ 3 * Real.pi / 2 at hdefect
  rw [integral_div]
  change Real.pi / 2 ≤ curvature / 2 + turning
  linarith only [htotal', hdefect]

end PoincareConjecture
