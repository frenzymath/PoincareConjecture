import PoincareConjecture.Proofs.M35.CapGeometry.InitialRadialEnds
import PoincareConjecture.Proofs.M35.CapGeometry.InitialCompactOperators
import PoincareConjecture.Proofs.M35.CapGeometry.InitialCoreVolume
import PoincareConjecture.Proofs.M35.CapGeometry.RadialCapNeighborhood

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

local notation "V" => StandardCapSpace

theorem exists_initial_radial_caps
    (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta epsilon Y : ℝ}
    (htheta : 0 < theta) (hthetalt : theta < E.flow.base.lifetime)
    (he : 0 < epsilon) (hehalf : epsilon < 1 / 2) (hY : 0 ≤ Y) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C ≥ C₀, ∀ t ∈ Icc 0 theta, ∀ x : V,
      radialArclength (E.flow.metric t) ‖x‖ ≤ Y →
        Nonempty (StandardCapNeighborhood E.atlas E.flow t epsilon C x) := by
  obtain ⟨A, hA, hends⟩ := exists_initial_radial_cap_ends
    P.curvature E htheta hthetalt he hehalf
  let a := A + Y + 2 * epsilon⁻¹ + 1
  have hel : 0 < epsilon⁻¹ := inv_pos.mpr he
  have ha : 0 < a := by dsimp only [a]; positivity
  have hAa : A ≤ a := by dsimp only [a]; linarith only [hY, hel]
  let Rmax := a + 2 * epsilon⁻¹
  have hRmax : 0 < Rmax := by dsimp only [Rmax]; positivity
  obtain ⟨K, hK, hcarrier⟩ := exists_initial_radial_carrier_compact
    P.curvature E ⟨htheta.le, hthetalt⟩ Rmax
  obtain ⟨B, hB, hbounds⟩ := exists_compact_initial_scalar_operator_bounds E
    ⟨htheta.le, hthetalt⟩ hK
  let F := 2 * E.initial_estimate.scalar_constant + 1
  have hF : 0 < F := by
    dsimp only [F]
    linarith only [E.initial_estimate.scalar_constant_pos]
  obtain ⟨Cv, hCv, hcorevolume⟩ := exists_initial_radial_ball_strict_volume P E
    ⟨htheta.le, hthetalt⟩ ha.le (show 0 ≤ 3 * F by positivity)
  let d := B ^ (-1 / 2 : ℝ)
  let v := B ^ (-3 / 2 : ℝ)
  have hd : 0 < d := Real.rpow_pos_of_pos hB _
  have hv : 0 < v := Real.rpow_pos_of_pos hB _
  let Vmax := Rmax ^ 3 * (Real.pi * 4 / 3)
  have hVmax : 0 < Vmax := by dsimp only [Vmax]; positivity
  let Cd := 2 * Rmax / d + 1
  let Cm := Vmax / v + 1
  have hCd : 0 < Cd := by dsimp only [Cd]; positivity
  have hCm : 0 < Cm := by dsimp only [Cm]; positivity
  let C₀ := Cv + B ^ 2 + B + Cd + Cm + 1
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  refine ⟨C₀, hC₀, ?_⟩
  intro C hC t ht x hx
  have hCpos : 0 < C := hC₀.trans_le hC
  have hCvC : Cv ≤ C := by dsimp only [C₀] at hC; nlinarith only [hC, hB, hCd, hCm]
  have hBC : B ≤ C := by dsimp only [C₀] at hC; nlinarith only [hC, hCv, hCd, hCm]
  have hBsC : B ^ 2 < C := by
    dsimp only [C₀] at hC
    linarith only [hC, hCv, hB, hCd, hCm]
  have hCdC : Cd ≤ C := by dsimp only [C₀] at hC; nlinarith only [hC, hCv, hB, hCm]
  have hCmC : Cm ≤ C := by dsimp only [C₀] at hC; nlinarith only [hC, hCv, hB, hCd]
  have htime : t ∈ Ico 0 E.flow.base.lifetime := ⟨ht.1, ht.2.trans_lt hthetalt⟩
  let g := E.flow.metric t
  let D := E.flow.connection t
  let hrot := E.rotation_invariant t htime
  let hc := E.complete t htime
  let Q := D.scalarCurvature
    (rawInverseRadius P.curvature E.flow.base E.rotation_invariant t a •
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
  let b := (Real.sqrt Q)⁻¹
  let a' := a - b * epsilon⁻¹
  let Q' := D.scalarCurvature
    (rawInverseRadius P.curvature E.flow.base E.rotation_invariant t a' •
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
  let b' := (Real.sqrt Q')⁻¹
  let R := a + b * epsilon⁻¹
  have hQ : 0 < Q := E.scalar_pos htime _
  have hQ' : 0 < Q' := E.scalar_pos htime _
  have hb : 0 < b := inv_pos.mpr (Real.sqrt_pos.mpr hQ)
  have hb' : 0 < b' := inv_pos.mpr (Real.sqrt_pos.mpr hQ')
  have hunit : Q * b ^ 2 = 1 := by
    dsimp only [b]
    rw [inv_pow, Real.sq_sqrt hQ.le, mul_inv_cancel₀ hQ.ne']
  have hunit' : Q' * b' ^ 2 = 1 := by
    dsimp only [b']
    rw [inv_pow, Real.sq_sqrt hQ'.le, mul_inv_cancel₀ hQ'.ne']
  obtain ⟨hend, hend', hbsmall, hspeed, hfar, hwidth⟩ := hends t ht a hAa
  change 0 < a' ∧ RoundCylinderClose epsilon 0 (radialCylinderTensor
    (fun u => Q * rawWarpingRadius P.curvature E.flow.base E.rotation_invariant t
      (a + b * u) ^ 2) 1) at hend
  change 0 < a' - b' * epsilon⁻¹ ∧ RoundCylinderClose epsilon 0 (radialCylinderTensor
    (fun u => Q' * rawWarpingRadius P.curvature E.flow.base E.rotation_invariant t
      (a' + b' * u) ^ 2) 1) at hend'
  have hfeq : rawWarpingRadius P.curvature E.flow.base E.rotation_invariant t =
      intrinsicWarpingRadius g hrot hc := by
    convert! rawWarpingRadius_eq P.curvature E.flow.base E.rotation_invariant htime using 1
  rw [hfeq] at hend hend' hfar hwidth
  have hR : 0 < R := by dsimp only [R]; positivity
  have hRR : R ≤ Rmax := by
    have h := mul_le_mul_of_nonneg_right hbsmall.le hel.le
    dsimp only [R, Rmax]
    linarith only [h]
  have hcenter : radialArclength g ‖x‖ < a' := by
    have h := mul_lt_mul_of_pos_right hbsmall hel
    dsimp only [a', a]
    linarith only [hx, h, hA]
  have hinside (y : V) (hy : y ∈ g.ball 0 R) : y ∈ K := by
    have hrad : radialArclength g ‖y‖ < R := by
      change g.edist 0 y < ENNReal.ofReal R at hy
      rw [edist_zero_eq_radialArclength g hrot hc P] at hy
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by
        simpa only [radialArclength_zero] using
          (radialArclength_strictMono g).monotone (norm_nonneg y)) |>.mp hy
    exact hcarrier t ht y (hrad.le.trans hRR)
  have hbound (y : V) (hy : y ∈ g.ball 0 R) := hbounds t ht y (hinside y hy)
  have hzero : (0 : V) ∈ g.ball 0 R := by
    change g.edist 0 0 < ENNReal.ofReal R
    rw [show g.edist 0 0 = 0 from @edist_self V g.toEMetricSpace.toPseudoEMetricSpace 0]
    exact ENNReal.ofReal_pos.mpr hR
  let S := scalarCurvatureSupOn g D (g.ball 0 R)
  have hbounded : BddAbove (range fun z : g.ball 0 R => D.scalarCurvature z.1) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact (hbound z z.property).2.1
  have hSpos : 0 < S := (E.scalar_pos htime 0).trans_le
    (le_csSup hbounded ⟨⟨0, hzero⟩, rfl⟩)
  have hSB : S ≤ B := by
    change sSup (range fun z : g.ball 0 R => D.scalarCurvature z.1) ≤ B
    apply csSup_le (s := range fun z : g.ball 0 R => D.scalarCurvature z.1)
      ⟨D.scalarCurvature 0, ⟨⟨0, hzero⟩, rfl⟩⟩
    rintro _ ⟨z, rfl⟩
    exact (hbound z z.property).2.1
  have hdS : d ≤ S ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hSpos hSB (by norm_num)
  have hvS : v ≤ S ^ (-3 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hSpos hSB (by norm_num)
  have hdiam : 2 * R ≤ C * S ^ (-1 / 2 : ℝ) := by
    have hCd' : 2 * Rmax / d < C := by dsimp only [Cd] at hCdC; linarith only [hCdC]
    exact (mul_le_mul_of_nonneg_left hRR (by norm_num)).trans
      (((div_lt_iff₀ hd).mp hCd').le.trans
        (mul_le_mul_of_nonneg_left hdS hCpos.le))
  have hvol : R ^ 3 * (Real.pi * 4 / 3) < C * S ^ (-3 / 2 : ℝ) := by
    have hCm' : Vmax / v < C := by dsimp only [Cm] at hCmC; linarith only [hCmC]
    have hRvol : R ^ 3 * (Real.pi * 4 / 3) ≤ Vmax :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR.le hRR 3) (by positivity)
    exact hRvol.trans_lt (((div_lt_iff₀ hv).mp hCm').trans_le
      (mul_le_mul_of_nonneg_left hvS hCpos.le))
  let q : UnitTwoSphere := ⟨EuclideanSpace.single (2 : Fin 3) (1 : ℝ), by simp⟩
  have hscalar (s : ℝ) (hs : 0 < s) :
      D.scalarCurvature (intrinsicSpatialInverse g hrot hc (s • q.val)) =
        D.scalarCurvature (rawInverseRadius P.curvature E.flow.base E.rotation_invariant
          t s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) := by
    rw [(rotational_scalar_edist_eq_axis P D hrot _).1,
      intrinsicSpatialInverse_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hs,
      norm_eq_of_mem_sphere, mul_one]
    congr 2
    convert! (rawInverseRadius_eq P.curvature E.flow.base E.rotation_invariant htime s).symm
      using 1
  refine ⟨radialCapNeighborhood P E t htime x q a b b' Q Q' epsilon C
    hb hb' hQ hQ' he hehalf hCpos hunit hunit' hend.1 hend'.1 hspeed hcenter
    (hscalar a ha) (hscalar a' hend.1) hend.2 hend'.2 hfar hwidth ?_ hdiam hvol ?_ ?_ ?_⟩
  · intro y hy z hz
    have hratio : B < C * B⁻¹ := by
      rw [← div_eq_mul_inv]
      apply (lt_div_iff₀ hB).mpr
      simpa only [pow_two] using hBsC
    exact (hbound z hz).2.1.trans_lt (hratio.trans_le
      (mul_le_mul_of_nonneg_left (hbound y hy).1 hCpos.le))
  · intro y hy r hr hrbound _hscale
    have hfbound : intrinsicWarpingRadius g hrot hc a ≤ F := by
      have h := raw_intrinsic_warping_controls P.curvature E.initial_estimate E.flow.base
        htime hrot a ha
      have hsq : intrinsicWarpingRadius g hrot hc a ^ 2 ≤
          2 * E.initial_estimate.scalar_constant := h.2.1
      dsimp only [F]
      nlinarith only [hsq, sq_nonneg (intrinsicWarpingRadius g hrot hc a - 1)]
    exact hcorevolume C hCvC t ht y (by
      change radialArclength g ‖y‖ ≤ a
      have hw : 0 < b * epsilon⁻¹ := mul_pos hb hel
      linarith only [hy, hw]) r hr
      (hrbound.trans (mul_le_mul_of_nonneg_left hfbound (by norm_num)))
  · intro y hy
    exact (hbound y hy).2.2.1.trans_le (mul_le_mul_of_nonneg_right hBC
      (Real.rpow_nonneg (E.scalar_pos htime y).le _))
  · intro y hy
    exact (hbound y hy).2.2.2.trans_le (mul_le_mul_of_nonneg_right hBC (sq_nonneg _))

end PoincareConjecture.M35.Uniqueness
