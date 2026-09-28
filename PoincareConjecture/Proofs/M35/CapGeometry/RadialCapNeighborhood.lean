import PoincareConjecture.Proofs.M35.CapGeometry.ScalarRadialNeck
import PoincareConjecture.Proofs.M35.CapGeometry.RadialCapBoundary
import PoincareConjecture.Proofs.M35.CapGeometry.RadialBallVolume
import PoincareConjecture.Proofs.M35.CapGeometry.RadialCoreCurvatureBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.Uniqueness

local notation "V" => StandardCapSpace





noncomputable def radialCapNeighborhood
    (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) (t : ℝ)
    (ht : t ∈ Ico 0 E.flow.base.lifetime) (x : V) (q : UnitTwoSphere)
    (a b b' Q Q' epsilon C : ℝ)
    (hb : 0 < b) (hb' : 0 < b') (hQ : 0 < Q) (hQ' : 0 < Q')
    (he : 0 < epsilon) (hehalf : epsilon < 1 / 2) (hC : 0 < C)
    (hunit : Q * b ^ 2 = 1) (hunit' : Q' * b' ^ 2 = 1)
    (hinner : 0 < a - b * epsilon⁻¹)
    (hinner' : 0 < (a - b * epsilon⁻¹) - b' * epsilon⁻¹)
    (hspeed : b' < 2 * b)
    (hcenter : radialArclength (E.flow.metric t) ‖x‖ < a - b * epsilon⁻¹)
    (hscalar : (E.flow.connection t).scalarCurvature
      (intrinsicSpatialInverse (E.flow.metric t) (E.rotation_invariant t ht)
        (E.complete t ht) (a • q.val)) = Q)
    (hscalar' : (E.flow.connection t).scalarCurvature
      (intrinsicSpatialInverse (E.flow.metric t) (E.rotation_invariant t ht)
        (E.complete t ht) ((a - b * epsilon⁻¹) • q.val)) = Q')
    (hend : RoundCylinderClose epsilon 0 (radialCylinderTensor
      (fun u => Q * intrinsicWarpingRadius (E.flow.metric t)
        (E.rotation_invariant t ht) (E.complete t ht) (a + b * u) ^ 2) 1))
    (hboundary : RoundCylinderClose epsilon 0 (radialCylinderTensor
      (fun u => Q' * intrinsicWarpingRadius (E.flow.metric t)
        (E.rotation_invariant t ht) (E.complete t ht)
          ((a - b * epsilon⁻¹) + b' * u) ^ 2) 1))
    (hfar : 6 * intrinsicWarpingRadius (E.flow.metric t)
      (E.rotation_invariant t ht) (E.complete t ht) a < a)
    (hwidth : intrinsicWarpingRadius (E.flow.metric t)
      (E.rotation_invariant t ht) (E.complete t ht) a < 2 * (b * epsilon⁻¹))
    (hratio : ∀ y ∈ (E.flow.metric t).ball 0 (a + b * epsilon⁻¹),
      ∀ z ∈ (E.flow.metric t).ball 0 (a + b * epsilon⁻¹),
        (E.flow.connection t).scalarCurvature z <
          C * (E.flow.connection t).scalarCurvature y)
    (hdiameter : 2 * (a + b * epsilon⁻¹) ≤ C *
      scalarCurvatureSupOn (E.flow.metric t) (E.flow.connection t)
        ((E.flow.metric t).ball 0 (a + b * epsilon⁻¹)) ^ (-1 / 2 : ℝ))
    (hvolume : (a + b * epsilon⁻¹) ^ 3 * (Real.pi * 4 / 3) < C *
      scalarCurvatureSupOn (E.flow.metric t) (E.flow.connection t)
        ((E.flow.metric t).ball 0 (a + b * epsilon⁻¹)) ^ (-3 / 2 : ℝ))
    (hcorevolume : ∀ y : V, radialArclength (E.flow.metric t) ‖y‖ < a - b * epsilon⁻¹ →
      ∀ r : ℝ, 0 < r → r ≤ 3 * intrinsicWarpingRadius (E.flow.metric t)
        (E.rotation_invariant t ht) (E.complete t ht) a →
      scalarCurvatureSupOn (E.flow.metric t) (E.flow.connection t)
        ((E.flow.metric t).ball y r) = r⁻¹ ^ 2 →
      ENNReal.ofReal (C⁻¹ * r ^ 3) <
        calibratedMetricVolume (E.flow.metric t) ((E.flow.metric t).ball y r))
    (hgradient : ∀ y ∈ (E.flow.metric t).ball 0 (a + b * epsilon⁻¹),
      scalarGradientNorm (E.flow.metric t) (E.flow.connection t) y <
        C * (E.flow.connection t).scalarCurvature y ^ (3 / 2 : ℝ))
    (hevolution : ∀ y ∈ (E.flow.metric t).ball 0 (a + b * epsilon⁻¹),
      |(E.flow.connection t).laplacian (E.flow.connection t).scalarCurvature y +
        2 * (E.flow.connection t).ricciNormSq y| <
          C * (E.flow.connection t).scalarCurvature y ^ 2) :
    StandardCapNeighborhood E.atlas E.flow t epsilon C x := by
  classical
  apply Classical.choice
  let g := E.flow.metric t
  let D := E.flow.connection t
  let hrot := E.rotation_invariant t ht
  let hc := E.complete t ht
  let R := a + b * epsilon⁻¹
  let s := a - b * epsilon⁻¹
  have hl : 0 < epsilon⁻¹ := inv_pos.mpr he
  have hw : 0 < b * epsilon⁻¹ := mul_pos hb hl
  have ha : 0 < a := by linarith only [hinner, hw]
  have hR : 0 < R := by dsimp only [R]; linarith only [ha, hw]
  let N := scalarRadialNeck g hrot hc E.atlas D Q hQ q a b epsilon
    hb he hehalf hunit hinner hscalar hend
  let N' := scalarRadialNeck g hrot hc E.atlas D Q' hQ' q s b' epsilon
    hb' he hehalf hunit' hinner' hscalar' hboundary
  obtain ⟨f, fi, hfrange, hfleft, hfright, hfsmooth, hfismooth⟩ :=
    radial_metric_ball_carrier_witness g hrot hc P hR
  obtain ⟨core, hcoresmooth, hcoreinj, hcoreimmersion, hcoreimage, hcoreboundary⟩ :=
    radial_metric_ball_closed_core_witness g hrot hc P hinner
  refine ⟨{
    time_mem := ht
    epsilon_pos := he
    epsilon_lt_half := hehalf
    constant_pos := hC
    carrier := g.ball 0 R
    carrier_open := ?_
    ball_map := f
    ball_inverse := fi
    ball_map_range := hfrange
    ball_map_left_inverse := hfleft
    ball_map_right_inverse := hfright
    ball_map_smooth := hfsmooth
    ball_inverse_smooth := hfismooth
    end_neck := N
    end_subset := ?_
    closed_core := closure (g.ball 0 s)
    closed_core_eq := ?_
    core_compact := radial_metric_ball_core_compact g hrot hc P hinner
    center_in_core := mem_interior_radial_core g hrot hc P hinner hcenter
    core_map := core
    core_map_smooth := hcoresmooth
    core_map_injective := hcoreinj
    core_map_immersion := hcoreimmersion
    core_map_image := hcoreimage
    core_boundary := hcoreboundary
    boundary_neck := N'
    boundary_neck_subset := ?_
    boundary_sphere := ?_
    scalar_pos := fun y _ => E.scalar_pos ht y
    scalar_ratio := hratio
    diameter_bound := ?_
    volume_bound := ?_
    core_ball := ?_
    gradient_bound := hgradient
    time_derivative_bound := hevolution
  }⟩
  · rw [ball_zero_eq_radial_ball g hrot hc P R]
    exact isOpen_ball
  · change (intrinsicRadialAnnulusPatch g hrot hc q a b epsilon⁻¹
      hb hl hinner).carrier ⊆ g.ball 0 R
    rw [intrinsicRadialAnnulusPatch_carrier]
    intro y hy
    change g.edist 0 y < ENNReal.ofReal R
    rw [edist_zero_eq_radialArclength g hrot hc P]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by
      simpa only [radialArclength_zero] using
        (radialArclength_strictMono g).monotone (norm_nonneg y))).mpr hy.2
  · exact intrinsicRadialAnnulusPatch_closed_core_eq g hrot hc P q a b epsilon⁻¹
      hb hl hinner
  · exact radial_boundary_neck_subset_outer_ball g hrot hc P q a b b' epsilon⁻¹
      hb' hl hinner' hspeed
  · exact radial_boundary_neck_frontier g hrot hc P q s b' epsilon⁻¹ hb' hl hinner'
  · intro y hy z hz
    exact (radial_ball_intrinsic_diameter g D hrot hc
      (E.nonnegative_sectional t ht) P hy hz).trans_le
        (ENNReal.ofReal_le_ofReal hdiameter)
  · have hv := radial_ball_volume_le g D hrot hc (E.nonnegative_sectional t ht) P R
    rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow hR.le,
      ← ENNReal.ofReal_mul (pow_nonneg hR.le 3)] at hv
    exact hv.trans_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr hvolume)
  · intro y hy
    have hr : 0 < (radialArclengthOrderIso g hrot hc).symm s := by
      simpa only [radialArclengthOrderIso_symm_zero] using
        (radialArclengthOrderIso g hrot hc).symm.strictMono hinner
    rw [closure_ball_zero_eq_radial_closedBall g hrot hc P hinner,
      interior_closedBall 0 hr.ne', mem_ball, dist_zero_right] at hy
    have hys : radialArclength g ‖y‖ < s := by
      change (radialArclengthOrderIso g hrot hc) ‖y‖ < s
      simpa only [OrderIso.apply_symm_apply] using
        (radialArclengthOrderIso g hrot hc).strictMono hy
    have hscalarcont : Continuous D.scalarCurvature :=
      (Proofs.M09.scalarCurvature_contMDiff P.curvature D).continuous
    obtain ⟨r, hrpos, hrbound, hrscale, hrinside, hrcompact⟩ :=
      radial_core_curvature_balls P g D hrot hc (E.nonnegative_sectional t ht)
        ha hw hfar hwidth hscalarcont y hys
    exact ⟨r, hrpos, hrscale, hrinside, hrcompact,
      hcorevolume y hys r hrpos hrbound hrscale⟩

end PoincareConjecture.M35.Uniqueness
