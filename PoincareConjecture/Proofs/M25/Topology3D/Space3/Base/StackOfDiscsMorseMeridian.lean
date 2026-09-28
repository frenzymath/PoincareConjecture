import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCanonicalGeometry
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem stackMorseMeridian_geometry
    (rFlat rOne v0 v1 rho lambda : ℝ)
    (hrFlat : 0 < rFlat) (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1)
    (hgap : v1 ^ 2 + rOne ^ 2 < 1)
    (hrho : 0 < rho) (hlambda : 0 < lambda) (hsmall : lambda < rho ^ 2 / 2) :
    let R := fun v => (stackCanonicalMeridian rFlat rOne v0 v1 v).1
    let Z := fun v => (stackCanonicalMeridian rFlat rOne v0 v1 v).2
    let w := fun v => Real.sqrt (rho ^ 2 + lambda * Z v) * R v
    Continuous w ∧ w (-1) = 0 ∧ w 0 = rho ∧
      (∀ v ∈ Icc (-1 : ℝ) 0,
        0 ≤ R v ∧ R v ≤ 1 ∧ -1 ≤ Z v ∧ Z v ≤ 0 ∧
        0 < rho ^ 2 + lambda * Z v ∧
        0 ≤ w v ∧ w v ≤ rho ∧
        w v ^ 2 ≤ rho ^ 2 + lambda * Z v) ∧
      (∀ v ∈ Ioc (-1 : ℝ) 0,
        HasDerivAt w
          (Real.sqrt (rho ^ 2 + lambda * Z v) * deriv R v +
            lambda * deriv Z v * R v /
              (2 * Real.sqrt (rho ^ 2 + lambda * Z v))) v ∧
        0 < deriv w v) ∧
      StrictMonoOn w (Icc (-1 : ℝ) 0) ∧
      w '' Icc (-1 : ℝ) 0 = Icc 0 rho := by
  let R := fun v => (stackCanonicalMeridian rFlat rOne v0 v1 v).1
  let Z := fun v => (stackCanonicalMeridian rFlat rOne v0 v1 v).2
  let w := fun v => Real.sqrt (rho ^ 2 + lambda * Z v) * R v
  have hrOnepos : 0 < rOne := hrFlat.trans hradii
  have hr01sq : rFlat ^ 2 < rOne ^ 2 :=
    (sq_lt_sq₀ hrFlat.le hrOnepos.le).mpr hradii
  have hr1sq : rOne ^ 2 < 1 := by
    simpa only [one_pow] using (sq_lt_sq₀ hrOnepos.le zero_le_one).mpr hrOne
  obtain ⟨ha, hapos, _, _, hanear, _, _⟩ :=
    stackCanonicalHorizontal_spec v0 v1 hv0 hv01 hv1
  obtain ⟨hb, _, _, _, _, _⟩ :=
    stackCanonicalFactor_spec (rFlat ^ 2) (rOne ^ 2) hr01sq hr1sq
  obtain ⟨hRf, hZf⟩ := stackCanonicalMeridian_formula
    rFlat rOne v0 v1 hrFlat hradii hrOne hv0 hv01 hv1 hgap
  have hRc : Continuous R := ha.continuous.mul
    (Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2)))
  have hZc : Continuous Z := (hb.continuous.comp (hRc.pow 2)).mul continuous_id
  have hwc : Continuous w :=
    (Real.continuous_sqrt.comp (continuous_const.add (continuous_const.mul hZc))).mul hRc
  have hpole : w (-1) = 0 := by
    simp only [w, R, stackCanonicalMeridian]
    norm_num
  have hRzero : R 0 = 1 := by
    have h := hanear 0 (by simpa using hv0.le)
    simpa only [R, stackCanonicalMeridian, zero_pow (by norm_num : 2 ≠ 0),
      sub_zero, Real.sqrt_one, mul_one, inv_one] using h
  have hZzero : Z 0 = 0 := by simp only [Z, stackCanonicalMeridian, mul_zero]
  have hzero : w 0 = rho := by
    simp only [w, hRzero, hZzero, mul_zero, add_zero, mul_one, Real.sqrt_sq hrho.le]
  have hbounds (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 0) :
      0 ≤ R v ∧ R v ≤ 1 ∧ -1 ≤ Z v ∧ Z v ≤ 0 ∧
      0 < rho ^ 2 + lambda * Z v ∧
      0 ≤ w v ∧ w v ≤ rho ∧ w v ^ 2 ≤ rho ^ 2 + lambda * Z v := by
    have hRnonneg : 0 ≤ R v := mul_nonneg (hapos v).le (Real.sqrt_nonneg _)
    have hRle : R v ≤ 1 := by
      rw [show R v = _ from hRf v]
      have hsqrt : Real.sqrt (1 - v ^ 2) ≤ 1 :=
        Real.sqrt_le_one.mpr (by linarith only [sq_nonneg v])
      exact sub_le_self _ (mul_nonneg (Real.smoothTransition.nonneg _)
        (sub_nonneg.mpr hsqrt))
    have hZlo : -1 ≤ Z v := by
      rw [show Z v = _ from hZf v hv]
      linarith only [mul_nonneg (show 0 ≤ v + 1 by linarith only [hv.1])
        (Real.smoothTransition.nonneg
          ((1 - v ^ 2 - rFlat ^ 2) / (rOne ^ 2 - rFlat ^ 2)))]
    have hZhi : Z v ≤ 0 := by
      rw [show Z v = _ from hZf v hv]
      have h := mul_le_mul (show v + 1 ≤ 1 by linarith only [hv.2])
        (Real.smoothTransition.le_one
          ((1 - v ^ 2 - rFlat ^ 2) / (rOne ^ 2 - rFlat ^ 2)))
        (Real.smoothTransition.nonneg _) zero_le_one
      linarith only [h]
    have hrad : 0 < rho ^ 2 + lambda * Z v := by
      have h := mul_le_mul_of_nonneg_left hZlo hlambda.le
      nlinarith only [h, hsmall, sq_nonneg rho, hlambda]
    have hw0 : 0 ≤ w v := mul_nonneg (Real.sqrt_nonneg _) hRnonneg
    have hwsq : w v ^ 2 = (rho ^ 2 + lambda * Z v) * R v ^ 2 := by
      dsimp only [w]
      rw [mul_pow, Real.sq_sqrt hrad.le]
    have hwsqle : w v ^ 2 ≤ rho ^ 2 + lambda * Z v := by
      have hR2 : R v ^ 2 ≤ 1 := by nlinarith only [hRnonneg, hRle]
      have h := mul_le_mul_of_nonneg_left hR2 hrad.le
      simpa only [mul_one, ← hwsq] using h
    have hwle : w v ≤ rho := by
      have h := mul_nonpos_of_nonneg_of_nonpos hlambda.le hZhi
      nlinarith only [hwsqle, h, hrho, hw0]
    exact ⟨hRnonneg, hRle, hZlo, hZhi, hrad, hw0, hwle, hwsqle⟩
  have hderiv (v : ℝ) (hv : v ∈ Ioc (-1 : ℝ) 0) :
      HasDerivAt w
        (Real.sqrt (rho ^ 2 + lambda * Z v) * deriv R v +
          lambda * deriv Z v * R v /
            (2 * Real.sqrt (rho ^ 2 + lambda * Z v))) v ∧
      0 < deriv w v := by
    obtain ⟨hRd, hZd, hRnonneg, hZnonneg, hstrict⟩ := stackCanonicalMeridian_regular
      rFlat rOne v0 v1 hrFlat hradii hrOne hv0 hv01 hv1 hgap v hv
    have hrad := (hbounds v ⟨hv.1.le, hv.2⟩).2.2.2.2.1
    have hsqrt : 0 < Real.sqrt (rho ^ 2 + lambda * Z v) := Real.sqrt_pos.mpr hrad
    have hRpos : 0 < R v := by
      apply mul_pos (hapos v) (Real.sqrt_pos.mpr ?_)
      have habs : |v| < 1 := abs_lt.mpr ⟨hv.1, hv.2.trans_lt zero_lt_one⟩
      have hsq := (sq_lt_sq₀ (abs_nonneg v) zero_le_one).mpr habs
      simp only [sq_abs, one_pow] at hsq
      linarith only [hsq]
    have hradD : HasDerivAt (fun x => rho ^ 2 + lambda * Z x)
        (lambda * deriv Z v) v :=
      (hZd.hasDerivAt.const_mul lambda).const_add (rho ^ 2)
    have hwd : HasDerivAt w
        (Real.sqrt (rho ^ 2 + lambda * Z v) * deriv R v +
          lambda * deriv Z v * R v /
            (2 * Real.sqrt (rho ^ 2 + lambda * Z v))) v := by
      exact ((hradD.sqrt hrad.ne').mul hRd.hasDerivAt).congr_deriv (by ring)
    refine ⟨hwd, ?_⟩
    rw [hwd.deriv]
    have hfirst := mul_nonneg hsqrt.le hRnonneg
    have hsecond := div_nonneg (mul_nonneg (mul_nonneg hlambda.le hZnonneg) hRpos.le)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hsqrt.le)
    rcases hstrict with hRstrict | hZstrict
    · exact add_pos_of_pos_of_nonneg (mul_pos hsqrt hRstrict) hsecond
    · exact add_pos_of_nonneg_of_pos hfirst
        (div_pos (mul_pos (mul_pos hlambda hZstrict) hRpos)
          (mul_pos (by norm_num : (0 : ℝ) < 2) hsqrt))
  have hmono : StrictMonoOn w (Icc (-1 : ℝ) 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (-1) 0) hwc.continuousOn
    intro v hv
    rw [interior_Icc] at hv
    exact (hderiv v ⟨hv.1, hv.2.le⟩).2
  refine ⟨hwc, hpole, hzero, hbounds, hderiv, hmono, ?_⟩
  simpa only [hpole, hzero] using ContinuousOn.image_Icc_of_monotoneOn
    (by norm_num : (-1 : ℝ) ≤ 0) hwc.continuousOn hmono.monotoneOn

theorem stackMorseMeridian_pole_and_seam
    (rFlat rOne v0 v1 rho lambda : ℝ)
    (hrFlat : 0 < rFlat) (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1)
    (hgap : v1 ^ 2 + rOne ^ 2 < 1)
    (hrho : 0 < rho) (hlambda : 0 < lambda) (hsmall : lambda < rho ^ 2 / 2) :
    let R := fun v => (stackCanonicalMeridian rFlat rOne v0 v1 v).1
    let Z := fun v => (stackCanonicalMeridian rFlat rOne v0 v1 v).2
    let w := fun v => Real.sqrt (rho ^ 2 + lambda * Z v) * R v
    0 < Real.sqrt (rho ^ 2 - lambda) ∧
      (∃ vPole : ℝ, -1 < vPole ∧ vPole < -v1 ∧
        ∀ v ∈ Icc (-1 : ℝ) vPole,
          R v = Real.sqrt (1 - v ^ 2) ∧ Z v = -1 ∧
          w v = Real.sqrt (rho ^ 2 - lambda) * Real.sqrt (1 - v ^ 2)) ∧
      (∀ v ∈ Icc (-v0) 0,
        R v = 1 ∧ Z v = v ∧ w v = Real.sqrt (rho ^ 2 + lambda * v) ∧
        w v ^ 2 = rho ^ 2 + lambda * v) := by
  let R := fun v => (stackCanonicalMeridian rFlat rOne v0 v1 v).1
  let Z := fun v => (stackCanonicalMeridian rFlat rOne v0 v1 v).2
  let w := fun v => Real.sqrt (rho ^ 2 + lambda * Z v) * R v
  have hrOnepos : 0 < rOne := hrFlat.trans hradii
  have hv1pos : 0 < v1 := hv0.trans hv01
  have hr01sq : rFlat ^ 2 < rOne ^ 2 :=
    (sq_lt_sq₀ hrFlat.le hrOnepos.le).mpr hradii
  have hr1sq : rOne ^ 2 < 1 := by
    simpa only [one_pow] using (sq_lt_sq₀ hrOnepos.le zero_le_one).mpr hrOne
  obtain ⟨_, _, _, _, hanear, hafar, _⟩ :=
    stackCanonicalHorizontal_spec v0 v1 hv0 hv01 hv1
  obtain ⟨_, _, _, hbfar, _, _⟩ :=
    stackCanonicalFactor_spec (rFlat ^ 2) (rOne ^ 2) hr01sq hr1sq
  have hZformula := (stackCanonicalMeridian_formula
    rFlat rOne v0 v1 hrFlat hradii hrOne hv0 hv01 hv1 hgap).2
  have hgeom := stackMorseMeridian_geometry rFlat rOne v0 v1 rho lambda
    hrFlat hradii hrOne hv0 hv01 hv1 hgap hrho hlambda hsmall
  have hroot : 0 < Real.sqrt (rho ^ 2 - lambda) := by
    apply Real.sqrt_pos.mpr
    nlinarith only [hsmall, hlambda]
  refine ⟨hroot, ?_, ?_⟩
  · let t := rFlat / 2
    have ht : 0 < t := by dsimp only [t]; linarith only [hrFlat]
    have htr : t < rFlat := by dsimp only [t]; linarith only [hrFlat]
    have ht1 : t < 1 := htr.trans (hradii.trans hrOne)
    have ht2 : t ^ 2 < 1 := by
      simpa only [one_pow] using (sq_lt_sq₀ ht.le zero_le_one).mpr ht1
    have htsq : t ^ 2 < rFlat ^ 2 := (sq_lt_sq₀ ht.le hrFlat.le).mpr htr
    have hspos : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr (sub_pos.mpr ht2)
    have hssq : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 :=
      Real.sq_sqrt (sub_nonneg.mpr ht2.le)
    have hslt : Real.sqrt (1 - t ^ 2) < 1 := by
      nlinarith only [hssq, hspos, sq_pos_of_pos ht]
    have hvlt : v1 < Real.sqrt (1 - t ^ 2) := by
      nlinarith only [hssq, hspos, hv1pos, hgap, htsq, hr01sq]
    refine ⟨-Real.sqrt (1 - t ^ 2), by linarith only [hslt],
      neg_lt_neg hvlt, ?_⟩
    intro v hv
    have hvneg : v < 0 := hv.2.trans_lt (neg_neg_of_pos hspos)
    have habs : v1 ≤ |v| := by
      rw [abs_of_neg hvneg]
      linarith only [hv.2, hvlt]
    have hR : R v = Real.sqrt (1 - v ^ 2) := by
      change stackCanonicalHorizontal v0 v1 v * Real.sqrt (1 - v ^ 2) = _
      rw [hafar v habs, one_mul]
    have hvsq : Real.sqrt (1 - t ^ 2) ^ 2 ≤ v ^ 2 := by
      have h := (sq_le_sq₀ hspos.le (neg_nonneg.mpr hvneg.le)).mpr
        (show Real.sqrt (1 - t ^ 2) ≤ -v by linarith only [hv.2])
      simpa only [neg_sq] using h
    have harg : (1 - v ^ 2 - rFlat ^ 2) / (rOne ^ 2 - rFlat ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (by linarith only [hvsq, hssq, htsq]) (sub_nonneg.mpr hr01sq.le)
    have hZ : Z v = -1 := by
      rw [show Z v = _ from hZformula v ⟨hv.1, hvneg.le⟩,
        Real.smoothTransition.zero_of_nonpos harg, mul_zero, add_zero]
    refine ⟨hR, hZ, ?_⟩
    change w v = Real.sqrt (rho ^ 2 - lambda) * Real.sqrt (1 - v ^ 2)
    simp only [w, hR, hZ, mul_neg_one, ← sub_eq_add_neg]
  · intro v hv
    have habs : |v| ≤ v0 := by
      rw [abs_of_nonpos hv.2]
      linarith only [hv.1]
    have hvabs : |v| < 1 := habs.trans_lt (hv01.trans hv1)
    have hvsq : v ^ 2 < 1 := by
      simpa only [sq_abs, one_pow] using (sq_lt_sq₀ (abs_nonneg v) zero_le_one).mpr hvabs
    have hspos : 0 < Real.sqrt (1 - v ^ 2) := Real.sqrt_pos.mpr (sub_pos.mpr hvsq)
    have hR : R v = 1 := by
      change stackCanonicalHorizontal v0 v1 v * Real.sqrt (1 - v ^ 2) = _
      rw [hanear v habs, inv_mul_cancel₀ hspos.ne']
    have hZ : Z v = v := by
      change stackCanonicalFactor (rFlat ^ 2) (rOne ^ 2) (R v ^ 2) * v = v
      rw [hR, one_pow, hbfar 1 hr1sq.le, one_mul]
    have hw : w v = Real.sqrt (rho ^ 2 + lambda * v) := by
      simp only [w, hR, hZ, mul_one]
    refine ⟨hR, hZ, hw, ?_⟩
    have hrad := (hgeom.2.2.2.1 v ⟨by linarith only [hv.1, hv01, hv1], hv.2⟩).2.2.2.2.1
    change 0 < rho ^ 2 + lambda * Z v at hrad
    rw [hZ] at hrad
    change w v ^ 2 = rho ^ 2 + lambda * v
    rw [hw, Real.sq_sqrt hrad.le]

end PoincareConjecture.M25.Topology3D
