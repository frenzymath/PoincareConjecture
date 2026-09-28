import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CompactField
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp










set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D




theorem exists_reference_ball_radial_correction :
    ∃ (rho : ℝ) (d : ℝ → ℝ),
      0 < rho ∧ rho ≤ 1 / 16 ∧
      ContDiff ℝ ∞ d ∧ HasCompactSupport d ∧
      tsupport d ⊆ Set.Ioo (-rho) rho ∧
      (∀ q : ℝ, 0 ≤ q → q ≤ rho / 2 →
        d q = Real.sqrt (1 - q) - 1 + q / 2) ∧
      (∀ q : ℝ, rho ≤ q → d q = 0) ∧
      (∀ q : ℝ, 0 ≤ q → -(q ^ 2) / 2 ≤ d q ∧ d q ≤ 0) ∧
      (∀ q : ℝ, 0 ≤ q → |deriv d q| ≤ 1 / 16) := by
  obtain ⟨chi, hchi, hsChi, hchiSupport, hchiNear, hchiRange⟩ :=
    exists_compact_smooth_cutoff
      (K := Icc (0 : ℝ) (1 / 2)) (U := Ioo (-1 : ℝ) 1)
      isCompact_Icc isOpen_Ioo (by
        intro v hv
        constructor <;> linarith [hv.1, hv.2])
  obtain ⟨C0, _L0, hLip, _hBound⟩ := compactField_bounds chi hchi hsChi
  let C : ℝ := C0
  have hC : 0 ≤ C := C0.coe_nonneg
  have hC2 : 0 < C + 2 := by linarith
  have hCden : 0 < 8 * (C + 2) := mul_pos (by norm_num) hC2
  have hchiDeriv (v : ℝ) : |deriv chi v| ≤ C := by
    simpa only [Real.norm_eq_abs, C] using
      (norm_deriv_le_of_lipschitz (x₀ := v) hLip)
  have hchiOne (v : ℝ) (hv : v ∈ Icc (0 : ℝ) (1 / 2)) : chi v = 1 :=
    subset_of_mem_nhdsSet hchiNear hv
  let rho : ℝ := min (1 / 16) (1 / (8 * (C + 2)))
  have hrho : 0 < rho := lt_min (by norm_num) (one_div_pos.mpr hCden)
  have hrhoSmall : rho ≤ 1 / 16 := min_le_left _ _
  have hrhoBudget : rho ≤ 1 / (8 * (C + 2)) := min_le_right _ _
  have hrhoOne : rho < 1 := by linarith
  have hbudget : (C + 2) * rho / 2 ≤ 1 / 16 := by
    have h := (le_div_iff₀ hCden).mp hrhoBudget
    nlinarith
  let a : ℝ → ℝ := fun q => chi (q / rho)
  let f : ℝ → ℝ := fun q => Real.sqrt (1 - q) - 1 + q / 2
  let d : ℝ → ℝ := fun q => a q * f q
  have hscale : ContDiff ℝ ∞ (fun q : ℝ => q / rho) :=
    contDiff_id.div_const rho
  have ha : ContDiff ℝ ∞ a := hchi.comp hscale
  have haPreimage : tsupport a ⊆ (fun q : ℝ => q / rho) ⁻¹' tsupport chi := by
    apply closure_minimal ?_ ((isClosed_tsupport chi).preimage hscale.continuous)
    intro q hq
    exact subset_tsupport chi hq
  have haSupport : tsupport a ⊆ Ioo (-rho) rho := by
    intro q hq
    have h := hchiSupport (haPreimage hq)
    have hlo := (lt_div_iff₀ hrho).mp h.1
    have hhi := (div_lt_iff₀ hrho).mp h.2
    constructor <;> linarith
  have haCompact : HasCompactSupport a :=
    (isCompact_Icc : IsCompact (Icc (-rho) rho)).of_isClosed_subset
      (isClosed_tsupport a) (fun _ hq => ⟨(haSupport hq).1.le, (haSupport hq).2.le⟩)
  have haDomain : tsupport a ⊆ Iio (1 : ℝ) :=
    fun _ hq => (haSupport hq).2.trans hrhoOne
  have hroot : ContDiffOn ℝ ∞ (fun q : ℝ => Real.sqrt (1 - q)) (Iio 1) :=
    (contDiff_const.sub contDiff_id).contDiffOn.sqrt
      (fun _ hq => (sub_pos.mpr hq).ne')
  have hf : ContDiffOn ℝ ∞ f (Iio 1) :=
    (hroot.sub contDiffOn_const).add (contDiff_id.div_const (2 : ℝ)).contDiffOn
  have hd : ContDiff ℝ ∞ d := by
    simpa only [smul_eq_mul] using
      (contDiff_cutoff_smul isOpen_Iio a ha haDomain f hf)
  have hdLeft : tsupport d ⊆ tsupport a := tsupport_mul_subset_left
  have hdSupport : tsupport d ⊆ Ioo (-rho) rho := hdLeft.trans haSupport
  have hdCompact : HasCompactSupport d :=
    haCompact.isCompact.of_isClosed_subset (isClosed_tsupport d) hdLeft
  have hnotSupport (q : ℝ) (hq : rho ≤ q) : q ∉ tsupport d :=
    fun hqSupport => (not_lt_of_ge hq) (hdSupport hqSupport).2
  have hfar (q : ℝ) (hq : rho ≤ q) : d q = 0 :=
    image_eq_zero_of_notMem_tsupport (hnotSupport q hq)
  have heq (q : ℝ) (hq0 : 0 ≤ q) (hqr : q ≤ rho / 2) :
      d q = Real.sqrt (1 - q) - 1 + q / 2 := by
    have harg : q / rho ∈ Icc (0 : ℝ) (1 / 2) :=
      ⟨div_nonneg hq0 hrho.le, (div_le_iff₀ hrho).mpr (by linarith)⟩
    have hOne : a q = 1 := hchiOne (q / rho) harg
    change a q * f q = f q
    rw [hOne, one_mul]
  have haDeriv (q : ℝ) :
      HasDerivAt a (deriv chi (q / rho) / rho) q := by
    have h := ((hchi.differentiable (by simp) (q / rho)).hasDerivAt).comp q
      ((hasDerivAt_id q).div_const rho)
    simpa only [a, Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using h
  have haDerivBound (q : ℝ) : |deriv a q| ≤ C / rho := by
    rw [(haDeriv q).deriv, abs_div, abs_of_pos hrho]
    exact div_le_div_of_nonneg_right (hchiDeriv (q / rho)) hrho.le
  have hfLocal (q : ℝ) (hq0 : 0 ≤ q) (hqr : q ≤ rho) :
      DifferentiableAt ℝ f q ∧ -(q ^ 2) / 2 ≤ f q ∧ f q ≤ 0 ∧
        |f q| ≤ q ^ 2 / 2 ∧ |deriv f q| ≤ q := by
    let s : ℝ := Real.sqrt (1 - q)
    have hrad : 0 < 1 - q := by linarith
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs : 0 < s := Real.sqrt_pos.mpr hrad
    have hsSq : s ^ 2 = 1 - q := Real.sq_sqrt hrad.le
    have hsLower : (3 : ℝ) / 4 ≤ s := by
      apply Real.le_sqrt_of_sq_le
      nlinarith
    have hsUpper : s ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
    have hOneS : 0 < 1 + s := by positivity
    have hqSq : q = 1 - s ^ 2 := by linarith
    have hvalue : f q = -(q ^ 2) / (2 * (1 + s) ^ 2) := by
      change s - 1 + q / 2 = -(q ^ 2) / (2 * (1 + s) ^ 2)
      rw [hqSq]
      field_simp [hOneS.ne']
      ring
    have hden : 0 < 2 * (1 + s) ^ 2 := by positivity
    have hdenTwo : (2 : ℝ) ≤ 2 * (1 + s) ^ 2 := by
      nlinarith [sq_nonneg s]
    have hquot : q ^ 2 / (2 * (1 + s) ^ 2) ≤ q ^ 2 / 2 :=
      div_le_div_of_nonneg_left (sq_nonneg q) (by norm_num) hdenTwo
    have hlow : -(q ^ 2) / 2 ≤ f q := by
      rw [hvalue]
      simpa only [neg_div] using neg_le_neg hquot
    have hupp : f q ≤ 0 := by
      rw [hvalue]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg q)) hden.le
    have habs : |f q| ≤ q ^ 2 / 2 := by
      rw [abs_of_nonpos hupp]
      linarith
    have hsDeriv : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x))
        (-1 / (2 * s)) q := by
      exact ((hasDerivAt_id q).const_sub (1 : ℝ)).sqrt hrad.ne'
    have hfDeriv : HasDerivAt f (-1 / (2 * s) + 1 / 2) q :=
      (hsDeriv.sub_const 1).add ((hasDerivAt_id q).div_const 2)
    have hderiv : deriv f q = -q / (2 * s * (1 + s)) := by
      rw [hfDeriv.deriv, hqSq]
      field_simp [hs.ne', hOneS.ne']
      ring
    have hdenOne : (1 : ℝ) ≤ 2 * s * (1 + s) := by
      nlinarith [sq_nonneg s]
    have hdenPos : 0 < 2 * s * (1 + s) := lt_of_lt_of_le zero_lt_one hdenOne
    have hderivBound : |deriv f q| ≤ q := by
      rw [hderiv, abs_div, abs_neg, abs_of_nonneg hq0, abs_of_pos hdenPos]
      exact div_le_self hq0 hdenOne
    exact ⟨hfDeriv.differentiableAt, hlow, hupp, habs, hderivBound⟩
  refine ⟨rho, d, hrho, hrhoSmall, hd, hdCompact, hdSupport, heq, hfar, ?_, ?_⟩
  · intro q hq0
    by_cases hqr : q ≤ rho
    · obtain ⟨_hDiff, hlow, hupp, _habs, _hDeriv⟩ := hfLocal q hq0 hqr
      have har : 0 ≤ a q ∧ a q ≤ 1 := hchiRange (q / rho)
      have hfd : f q ≤ a q * f q := by
        simpa only [one_mul] using mul_le_mul_of_nonpos_right har.2 hupp
      exact ⟨hlow.trans hfd, mul_nonpos_of_nonneg_of_nonpos har.1 hupp⟩
    · rw [hfar q (le_of_lt (lt_of_not_ge hqr))]
      constructor
      · nlinarith [sq_nonneg q]
      · exact le_rfl
  · intro q hq0
    by_cases hqr : q ≤ rho
    · obtain ⟨hDiff, _hlow, _hupp, habs, hDeriv⟩ := hfLocal q hq0 hqr
      have har : 0 ≤ a q ∧ a q ≤ 1 := hchiRange (q / rho)
      have haAbs : |a q| ≤ 1 := by
        rw [abs_of_nonneg har.1]
        exact har.2
      have hprod : deriv d q = deriv a q * f q + a q * deriv f q :=
        (((ha.differentiable (by simp) q).hasDerivAt).mul hDiff.hasDerivAt).deriv
      have hCrho : 0 ≤ C / rho := div_nonneg hC hrho.le
      have hsq : q ^ 2 ≤ rho ^ 2 := (sq_le_sq₀ hq0 hrho.le).mpr hqr
      calc
        |deriv d q| = |deriv a q * f q + a q * deriv f q| := congrArg abs hprod
        _ ≤ |deriv a q * f q| + |a q * deriv f q| := abs_add_le _ _
        _ = |deriv a q| * |f q| + |a q| * |deriv f q| := by
          rw [abs_mul, abs_mul]
        _ ≤ (C / rho) * (q ^ 2 / 2) + 1 * q := add_le_add
          (mul_le_mul (haDerivBound q) habs (abs_nonneg _) hCrho)
          (mul_le_mul haAbs hDeriv (abs_nonneg _) zero_le_one)
        _ ≤ (C / rho) * (rho ^ 2 / 2) + rho := by
          simpa only [one_mul] using add_le_add
            (mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 2)) hCrho) hqr
        _ = (C + 2) * rho / 2 := by
          field_simp [hrho.ne']
        _ ≤ 1 / 16 := hbudget
    · rw [deriv_of_notMem_tsupport (hnotSupport q (le_of_lt (lt_of_not_ge hqr))),
        abs_zero]
      norm_num

end PoincareConjecture.M25.Topology3D
