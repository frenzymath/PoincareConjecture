import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMorseMeridian
import Mathlib.Tactic










set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower




theorem outer_cap_meridian_geometry
    (p : ℝ × ℝ → ℝ) (hp : ContDiff ℝ ∞ p)
    (hpzero : ∀ h : ℝ, p (h, 0) = 0)
    (hpr : ∀ h r : ℝ, 0 < deriv (fun s : ℝ => p (h, s)) r)
    (hph : ∀ h ∈ Ioo (17 / 16 - 1 / 16384 : ℝ) (17 / 16 + 1 / 16384),
      ∀ r : ℝ, 0 < r → deriv (fun s : ℝ => p (s, r)) h ≤ 0)
    (hphOne : ∀ h ∈ Ioo (17 / 16 - 1 / 16384 : ℝ) (17 / 16 + 1 / 16384),
      deriv (fun s : ℝ => p (s, 1)) h < 0)
    (h lambda : ℝ) (hh : |h - 17 / 16| ≤ 1 / 32768)
    (hlambda : 0 < lambda) (hsmall : lambda < 1 / 131072) :
    let R : ℝ → ℝ := fun v => (stackCanonicalMeridian (1 / 4) (1 / 2) (1 / 4) (1 / 2) v).1
    let Z : ℝ → ℝ := fun v => (stackCanonicalMeridian (1 / 4) (1 / 2) (1 / 4) (1 / 2) v).2
    let W : ℝ → ℝ := fun v => p (h - lambda * Z v, R v)
    Continuous W ∧ W (-1) = 0 ∧ W 0 = p (h, 1) ∧ 0 < p (h, 1) ∧
      (∀ v ∈ Icc (-1 : ℝ) 0,
        0 ≤ R v ∧ R v ≤ 1 ∧ -1 ≤ Z v ∧ Z v ≤ 0 ∧
        h - lambda * Z v ∈
          Ioo (17 / 16 - 1 / 16384 : ℝ) (17 / 16 + 1 / 16384)) ∧
      (∀ v ∈ Ioc (-1 : ℝ) 0,
        HasDerivAt W
          (deriv (fun s : ℝ => p (h - lambda * Z v, s)) (R v) * deriv R v -
            lambda * deriv (fun s : ℝ => p (s, R v)) (h - lambda * Z v) * deriv Z v) v ∧
        0 < deriv W v) ∧
      StrictMonoOn W (Icc (-1 : ℝ) 0) ∧
      W '' Icc (-1 : ℝ) 0 = Icc 0 (p (h, 1)) := by
  let R : ℝ → ℝ := fun v =>
    (stackCanonicalMeridian (1 / 4) (1 / 2) (1 / 4) (1 / 2) v).1
  let Z : ℝ → ℝ := fun v =>
    (stackCanonicalMeridian (1 / 4) (1 / 2) (1 / 4) (1 / 2) v).2
  let W : ℝ → ℝ := fun v => p (h - lambda * Z v, R v)
  obtain ⟨ha, hapos, _, _, hanear, _, _⟩ :=
    stackCanonicalHorizontal_spec (1 / 4) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hb, _, _, _, _, _⟩ :=
    stackCanonicalFactor_spec ((1 / 4 : ℝ) ^ 2) ((1 / 2 : ℝ) ^ 2)
      (by norm_num) (by norm_num)
  obtain ⟨hRf, _⟩ := stackCanonicalMeridian_formula (1 / 4) (1 / 2) (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hRc : Continuous R := ha.continuous.mul
    (Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2)))
  have hZc : Continuous Z := (hb.continuous.comp (hRc.pow 2)).mul continuous_id
  have hWc : Continuous W := hp.continuous.comp
    ((continuous_const.sub (continuous_const.mul hZc)).prodMk hRc)
  have hRpole : R (-1) = 0 := by
    simp only [R, stackCanonicalMeridian]
    norm_num
  have hRzero : R 0 = 1 := by
    have h0 := hanear 0 (by norm_num : |(0 : ℝ)| ≤ 1 / 4)
    simpa only [R, stackCanonicalMeridian, zero_pow (by norm_num : 2 ≠ 0),
      sub_zero, Real.sqrt_one, mul_one, inv_one] using h0
  have hZzero : Z 0 = 0 := by simp only [Z, stackCanonicalMeridian, mul_zero]
  have hWpole : W (-1) = 0 := by
    change p (h - lambda * Z (-1), R (-1)) = 0
    rw [hRpole, hpzero]
  have hWzero : W 0 = p (h, 1) := by
    change p (h - lambda * Z 0, R 0) = p (h, 1)
    rw [hZzero, hRzero, mul_zero, sub_zero]
  have hpOne : 0 < p (h, 1) := by
    have hm := strictMono_of_deriv_pos (hpr h)
    simpa only [hpzero] using hm (by norm_num : (0 : ℝ) < 1)
  obtain ⟨_, _, _, hcanonical, _, _, _⟩ :=
    stackMorseMeridian_geometry (1 / 4) (1 / 2) (1 / 4) (1 / 2) 1 (1 / 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hbounds (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 0) :
      0 ≤ R v ∧ R v ≤ 1 ∧ -1 ≤ Z v ∧ Z v ≤ 0 ∧
      h - lambda * Z v ∈
        Ioo (17 / 16 - 1 / 16384 : ℝ) (17 / 16 + 1 / 16384) := by
    obtain ⟨hRlo, hRhi, hZlo, hZhi, _⟩ := hcanonical v hv
    have hlo := mul_le_mul_of_nonneg_left hZlo hlambda.le
    have hhi := mul_le_mul_of_nonneg_left hZhi hlambda.le
    obtain ⟨hhlo, hhhi⟩ := abs_le.mp hh
    exact ⟨hRlo, hRhi, hZlo, hZhi, by dsimp only [Z]; constructor <;> linarith⟩

  have hRadius (v : ℝ) (hv : v ∈ Ioc (-1 : ℝ) 0) :
      0 < deriv R v ∨ R v = 1 := by
    let r : ℝ → ℝ := fun w => Real.sqrt (1 - w ^ 2)
    let k : ℝ → ℝ := fun w =>
      Real.smoothTransition ((w ^ 2 - (1 / 4 : ℝ) ^ 2) /
        ((1 / 2 : ℝ) ^ 2 - (1 / 4 : ℝ) ^ 2))
    have hdv : 0 < (1 / 2 : ℝ) ^ 2 - (1 / 4 : ℝ) ^ 2 := by norm_num
    have hvabs : |v| < 1 := abs_lt.mpr ⟨hv.1, hv.2.trans_lt zero_lt_one⟩
    have hvsq : v ^ 2 < 1 := by
      simpa only [sq_abs, one_pow] using
        (sq_lt_sq₀ (abs_nonneg v) zero_le_one).mpr hvabs
    have hrpos : 0 < r v := Real.sqrt_pos.mpr (sub_pos.mpr hvsq)
    have hrle : r v ≤ 1 := Real.sqrt_le_one.mpr (by linarith only [sq_nonneg v])
    have hdradius : HasDerivAt r (-v / r v) v := by
      have hd := ((hasDerivAt_const v (1 : ℝ)).sub (hasDerivAt_pow 2 v)).sqrt
        (sub_pos.mpr hvsq).ne'
      convert hd using 1 <;> dsimp only [r] <;> norm_num
      ring
    let kp := deriv Real.smoothTransition
      ((v ^ 2 - (1 / 4 : ℝ) ^ 2) / ((1 / 2 : ℝ) ^ 2 - (1 / 4 : ℝ) ^ 2)) *
      (2 * v / ((1 / 2 : ℝ) ^ 2 - (1 / 4 : ℝ) ^ 2))
    have hSc : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
    have hS : Differentiable ℝ Real.smoothTransition := hSc.differentiable (by simp)
    have hdk : HasDerivAt k kp v := by
      have hi : HasDerivAt (fun w : ℝ =>
          (w ^ 2 - (1 / 4 : ℝ) ^ 2) / ((1 / 2 : ℝ) ^ 2 - (1 / 4 : ℝ) ^ 2))
          (2 * v / ((1 / 2 : ℝ) ^ 2 - (1 / 4 : ℝ) ^ 2)) v := by
        exact (((hasDerivAt_pow 2 v).sub_const ((1 / 4 : ℝ) ^ 2)).div_const
          ((1 / 2 : ℝ) ^ 2 - (1 / 4 : ℝ) ^ 2)).congr_deriv (by norm_num)
      exact (hS _).hasDerivAt.comp v hi
    have hkp : kp ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
      Real.smoothTransition.monotone.deriv_nonneg
      (div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hv.2) hdv.le)
    have hRderiv : HasDerivAt R (-kp * (1 - r v) + k v * (-v / r v)) v := by
      have heq : R = fun w => 1 - k w * (1 - r w) := funext hRf
      rw [heq]
      exact ((hasDerivAt_const v (1 : ℝ)).sub
        (hdk.mul ((hasDerivAt_const v (1 : ℝ)).sub hdradius))).congr_deriv
          (by simp only [Pi.sub_apply]; ring)
    by_cases hkzero : k v = 0
    · right
      rw [show R v = 1 - k v * (1 - r v) from hRf v, hkzero, zero_mul, sub_zero]
    · left
      have hkpos : 0 < k v :=
        lt_of_le_of_ne (Real.smoothTransition.nonneg _) (Ne.symm hkzero)
      have hvneg : v < 0 := by
        apply lt_of_le_of_ne hv.2
        intro hz
        have harg : (v ^ 2 - (1 / 4 : ℝ) ^ 2) /
            ((1 / 2 : ℝ) ^ 2 - (1 / 4 : ℝ) ^ 2) ≤ 0 := by rw [hz]; norm_num
        exact hkzero (Real.smoothTransition.zero_of_nonpos harg)
      rw [hRderiv.deriv]
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (neg_nonneg.mpr hkp) (sub_nonneg.mpr hrle))
        (mul_pos hkpos (div_pos (neg_pos.mpr hvneg) hrpos))
  have hderiv (v : ℝ) (hv : v ∈ Ioc (-1 : ℝ) 0) :
      HasDerivAt W
        (deriv (fun s : ℝ => p (h - lambda * Z v, s)) (R v) * deriv R v -
          lambda * deriv (fun s : ℝ => p (s, R v)) (h - lambda * Z v) * deriv Z v) v ∧
      0 < deriv W v := by
    obtain ⟨hRd, hZd, hRnonneg, hZnonneg, hstrict⟩ :=
      stackCanonicalMeridian_regular (1 / 4) (1 / 2) (1 / 4) (1 / 2)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) v hv
    change DifferentiableAt ℝ R v at hRd
    change DifferentiableAt ℝ Z v at hZd
    change 0 ≤ deriv R v at hRnonneg
    change 0 ≤ deriv Z v at hZnonneg
    change 0 < deriv R v ∨ 0 < deriv Z v at hstrict
    have hRpos : 0 < R v := by
      apply mul_pos (hapos v) (Real.sqrt_pos.mpr ?_)
      have habs : |v| < 1 := abs_lt.mpr ⟨hv.1, hv.2.trans_lt zero_lt_one⟩
      have hsq := (sq_lt_sq₀ (abs_nonneg v) zero_le_one).mpr habs
      simp only [sq_abs, one_pow] at hsq
      linarith only [hsq]
    have hheight := (hbounds v ⟨hv.1.le, hv.2⟩).2.2.2.2
    let a := h - lambda * Z v
    let A := fderiv ℝ p (a, R v)
    have hpd : HasFDerivAt p A (a, R v) :=
      (hp.differentiable (by simp) (a, R v)).hasFDerivAt
    have hPa : HasDerivAt (fun s : ℝ => p (s, R v)) (A (1, 0)) a := by
      simpa only [Function.comp_def, id_eq] using hpd.comp_hasDerivAt a
        ((hasDerivAt_id a).prodMk (hasDerivAt_const a (R v)))
    have hPr : HasDerivAt (fun s : ℝ => p (a, s)) (A (0, 1)) (R v) := by
      simpa only [Function.comp_def, id_eq] using hpd.comp_hasDerivAt (R v)
        ((hasDerivAt_const (R v) a).prodMk (hasDerivAt_id (R v)))
    have hHd : HasDerivAt (fun w => h - lambda * Z w)
        (-(lambda * deriv Z v)) v := (hZd.hasDerivAt.const_mul lambda).const_sub h
    have hWd : HasDerivAt W
        (deriv (fun s : ℝ => p (a, s)) (R v) * deriv R v -
          lambda * deriv (fun s : ℝ => p (s, R v)) a * deriv Z v) v := by
      have hc := hpd.comp_hasDerivAt v (hHd.prodMk hRd.hasDerivAt)
      change HasDerivAt W (A (-(lambda * deriv Z v), deriv R v)) v at hc
      apply hc.congr_deriv
      rw [show (-(lambda * deriv Z v), deriv R v) =
          (-(lambda * deriv Z v)) • ((1, 0) : ℝ × ℝ) +
            deriv R v • ((0, 1) : ℝ × ℝ) by ext <;> simp]
      rw [map_add, map_smul, map_smul, ← hPa.deriv, ← hPr.deriv]
      simp only [smul_eq_mul]
      ring
    refine ⟨hWd, ?_⟩
    rw [hWd.deriv]
    have hfirst := mul_nonneg (hpr a (R v)).le hRnonneg
    have hheightSign := hph a hheight (R v) hRpos
    have hsecond : lambda * deriv (fun s : ℝ => p (s, R v)) a * deriv Z v ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hlambda.le hheightSign) hZnonneg
    by_cases hRstrict : 0 < deriv R v
    · exact sub_pos.mpr (hsecond.trans_lt (mul_pos (hpr a (R v)) hRstrict))
    · have hRunit := (hRadius v hv).resolve_left hRstrict
      have hZstrict := hstrict.resolve_left hRstrict
      have hunitSign := hphOne a hheight
      have hsecondStrict :
          lambda * deriv (fun s : ℝ => p (s, R v)) a * deriv Z v < 0 := by
        rw [hRunit]
        exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hlambda hunitSign) hZstrict
      exact sub_pos.mpr (hsecondStrict.trans_le hfirst)
  have hmono : StrictMonoOn W (Icc (-1 : ℝ) 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (-1) 0) hWc.continuousOn
    intro v hv
    rw [interior_Icc] at hv
    exact (hderiv v ⟨hv.1, hv.2.le⟩).2
  refine ⟨hWc, hWpole, hWzero, hpOne, hbounds, hderiv, hmono, ?_⟩
  simpa only [hWpole, hWzero] using ContinuousOn.image_Icc_of_monotoneOn
    (by norm_num : (-1 : ℝ) ≤ 0) hWc.continuousOn hmono.monotoneOn

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
