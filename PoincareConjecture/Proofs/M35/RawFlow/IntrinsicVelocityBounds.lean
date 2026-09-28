import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicRadialVelocity
import Mathlib.Analysis.Calculus.MeanValue











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g) (D : LeviCivitaData g)
  (hsec : D.NonnegativeSectionalCurvature)

include D hsec



theorem intrinsicRadialAcceleration_bounds {K : ℝ}
    (hK : ∀ x, D.curvatureTensorNorm x ≤ K) (s : ℝ) :
    intrinsicRadialAcceleration g hrotation hcomplete s ∈ Icc (-2 * K) 0 := by
  have hp (r : ℝ) (hr : 0 < r) :
      intrinsicRadialAcceleration g hrotation hcomplete r ∈ Icc (-2 * K) 0 := by
    let a := (radialArclengthOrderIso g hrotation hcomplete).symm r
    have ha : 0 < a := radialArclengthOrderIso_symm_pos g hrotation hcomplete hr
    obtain ⟨u, v, hu, hv, huv, hc⟩ := exists_axis_radial_sectional_plane D hrotation ha
    have hn := (D.abs_sectionalCurvature_le_curvatureTensorNorm
      (a • EuclideanSpace.single (2 : Fin 3) 1) u v).trans (hK _)
    simp only [LeviCivitaData.sectionalCurvature, hu, hv, huv, one_mul,
      zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, sub_zero, div_one] at hn
    rw [hc] at hn
    have hpos := div_nonneg (radialMixedCurvatureFactor_nonneg D hrotation hsec ha)
      (axisRadialCoefficient_pos g a).le
    rw [intrinsicRadialAcceleration_eq_sectional g hrotation hcomplete hr]
    change -2 * K ≤ -2 * (radialMixedCurvatureFactor g a / axisRadialCoefficient g a) ∧ _
    constructor <;> linarith [(abs_le.mp hn).2]
  have hz : intrinsicRadialAcceleration g hrotation hcomplete 0 ∈ Icc (-2 * K) 0 := by
    have hc := (intrinsicRadialAcceleration_contDiff g hrotation hcomplete).continuous
    have ht : Tendsto (intrinsicRadialAcceleration g hrotation hcomplete)
        (𝓝[>] 0) (𝓝 (intrinsicRadialAcceleration g hrotation hcomplete 0)) :=
      (hc.tendsto 0).mono_left inf_le_left
    have he : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioi 0 := self_mem_nhdsWithin
    exact isClosed_Icc.mem_of_tendsto ht (he.mono (fun r hr => hp r hr))
  rcases lt_trichotomy s 0 with hs | hs | hs
  · have h := hp (-s) (neg_pos.mpr hs)
    rwa [intrinsicRadialAcceleration_even g hrotation hcomplete s] at h
  · simpa only [hs] using hz
  · exact hp s hs

private theorem intrinsic_slope_bounds {s : ℝ} (hs : 0 < s) :
    0 ≤ deriv (intrinsicWarpingRadius g hrotation hcomplete) s ∧
      deriv (intrinsicWarpingRadius g hrotation hcomplete) s ≤ 1 ∧
      deriv (deriv (intrinsicWarpingRadius g hrotation hcomplete)) s ≤ 0 := by
  rw [(intrinsicWarpingRadius_hasDerivAt g hrotation hcomplete hs).deriv,
    (intrinsicWarpingRadius_deriv_hasDerivAt g hrotation hcomplete hs).deriv]
  have hr := radialArclengthOrderIso_symm_pos g hrotation hcomplete hs
  exact ⟨axisWarpingSlope_nonneg D hrotation hsec hcomplete hr,
    axisWarpingSlope_le_one D hrotation hsec hr,
    axisWarpingSecond_nonpos D hrotation hsec hr⟩



theorem intrinsicRadialVelocity_abs_le {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, D.curvatureTensorNorm x ≤ K) (s : ℝ) :
    |intrinsicRadialVelocity g hrotation hcomplete s| ≤ 10 * (K + 1) := by
  let f := intrinsicWarpingRadius g hrotation hcomplete
  let v := intrinsicRadialVelocity g hrotation hcomplete
  let a := intrinsicRadialAcceleration g hrotation hcomplete
  have hf : ContDiff ℝ ∞ f := intrinsicWarpingRadius_contDiff g hrotation hcomplete
  have hf1 : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hv : ContDiff ℝ ∞ v := intrinsicRadialVelocity_contDiff g hrotation hcomplete
  have hdz : deriv f 0 = 1 := (intrinsicWarpingRadius_hasDerivAt_zero g hrotation hcomplete).deriv
  have hfz : f 0 = 0 := intrinsicWarpingRadius_zero g hrotation hcomplete
  have hvz : v 0 = 0 := intrinsicRadialVelocity_zero g hrotation hcomplete
  have hacc (r : ℝ) : -2 * K ≤ a r ∧ a r ≤ 0 :=
    intrinsicRadialAcceleration_bounds g hrotation hcomplete D hsec hK r
  have hdv (r : ℝ) : deriv v r = a r :=
    (intrinsicRadialVelocity_hasDerivAt g hrotation hcomplete r).deriv
  have hsl (r : ℝ) (hr : 0 < r) : 0 ≤ deriv f r ∧ deriv f r ≤ 1 ∧ deriv (deriv f) r ≤ 0 :=
    intrinsic_slope_bounds g hrotation hcomplete D hsec hr
  have hfpos (r : ℝ) (hr : 0 < r) : 0 < f r :=
    intrinsicWarpingRadius_pos g hrotation hcomplete hr
  have hfle (r : ℝ) (hr : 0 ≤ r) : f r ≤ r := by
    have hb := (convex_Icc (0 : ℝ) r).image_sub_le_mul_sub_of_deriv_le
      hf.continuous.continuousOn (hf.differentiable (by simp)).differentiableOn
      (fun x hx => (hsl x
        (show x ∈ Ioo 0 r from by simpa only [interior_Icc] using hx).1).2.1)
      0 (left_mem_Icc.mpr hr) r (right_mem_Icc.mpr hr) hr
    simpa only [hfz, sub_zero, one_mul] using hb
  have hvbasic (r : ℝ) (hr : 0 ≤ r) : -2 * K * r ≤ v r ∧ v r ≤ 0 := by
    have hlo := (convex_Icc (0 : ℝ) r).mul_sub_le_image_sub_of_le_deriv
      hv.continuous.continuousOn (hv.differentiable (by simp)).differentiableOn
      (fun x _ => by rw [hdv]; exact (hacc x).1)
      0 (left_mem_Icc.mpr hr) r (right_mem_Icc.mpr hr) hr
    have hhi := (convex_Icc (0 : ℝ) r).image_sub_le_mul_sub_of_deriv_le
      hv.continuous.continuousOn (hv.differentiable (by simp)).differentiableOn
      (fun x _ => by rw [hdv]; exact (hacc x).2)
      0 (left_mem_Icc.mpr hr) r (right_mem_Icc.mpr hr) hr
    simpa only [hvz, sub_zero, zero_mul] using And.intro hlo hhi
  let d : ℝ := 1 / (2 * (K + 1))
  have hd : 0 < d := one_div_pos.mpr (mul_pos (by norm_num) (by linarith))
  have hd1 : d ≤ 1 := (div_le_one (by positivity : 0 < 2 * (K + 1))).mpr (by linarith)
  have hKd : K * d ≤ 1 / 2 := by
    dsimp only [d]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    field_simp
    nlinarith
  have hsecond (r : ℝ) (hr : r ∈ Ioo 0 d) : -K ≤ deriv (deriv f) r := by
    have ha := (hacc r).1
    have he : a r = 2 * deriv (deriv f) r / f r :=
      intrinsicRadialAcceleration_eq g hrotation hcomplete hr.1
    rw [he] at ha
    have hh := (le_div_iff₀ (hfpos r hr.1)).mp ha
    have hhf : f r ≤ 1 := (hfle r hr.1.le).trans (hr.2.le.trans hd1)
    nlinarith [mul_nonneg hK0 (sub_nonneg.mpr hhf)]
  have hhalf (r : ℝ) (hr : r ∈ Icc 0 d) : 1 / 2 ≤ deriv f r := by
    have hb := (convex_Icc (0 : ℝ) d).mul_sub_le_image_sub_of_le_deriv
      hf1.continuous.continuousOn (hf1.differentiable (by simp)).differentiableOn
      (fun x hx => hsecond x (by simpa only [interior_Icc] using hx))
      0 (left_mem_Icc.mpr hd.le) r hr hr.1
    rw [sub_zero, hdz] at hb
    nlinarith [mul_le_mul_of_nonneg_left hr.2 hK0]
  have hfhalf : d / 2 ≤ f d := by
    have hb := (convex_Icc (0 : ℝ) d).mul_sub_le_image_sub_of_le_deriv
      hf.continuous.continuousOn (hf.differentiable (by simp)).differentiableOn
      (fun x hx => hhalf x (interior_subset hx))
      0 (left_mem_Icc.mpr hd.le) d (right_mem_Icc.mpr hd.le) hd.le
    rw [sub_zero, hfz, sub_zero] at hb
    linarith only [hb]
  have hmono : MonotoneOn f (Ioi 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ioi 0) hf.continuous.continuousOn
      (hf.differentiable (by simp)).differentiableOn
      (fun x hx => (hsl x (interior_subset hx)).1)
  have htail : MonotoneOn (fun r => v r - 2 * deriv f r / f d) (Ici d) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici d)
      (hv.continuous.sub ((continuous_const.mul hf1.continuous).div_const (f d))).continuousOn
      (fun r _ => by
        have hh := (intrinsicRadialVelocity_hasDerivAt g hrotation hcomplete r).sub
          (((hf1.differentiable (by simp) r).hasDerivAt.const_mul 2).div_const (f d))
        exact hh.hasDerivWithinAt)
    intro r hr
    have hdr : d ≤ r := interior_subset hr
    have hr0 : 0 < r := hd.trans_le hdr
    have hfd := hfpos d hd
    have hfr := hfpos r hr0
    have hcomp : f d ≤ f r := hmono hd hr0 hdr
    change 0 ≤ a r - 2 * deriv (deriv f) r / f d
    rw [show a r = 2 * deriv (deriv f) r / f r from
      intrinsicRadialAcceleration_eq g hrotation hcomplete hr0]
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ hfd hfr).mpr
    exact mul_le_mul_of_nonpos_left hcomp
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (hsl r hr0).2.2)
  have hp (r : ℝ) (hr : 0 ≤ r) : |v r| ≤ 10 * (K + 1) := by
    rw [abs_of_nonpos (hvbasic r hr).2]
    by_cases hrd : r ≤ d
    · have hlo := (hvbasic r hr).1
      nlinarith [mul_le_mul_of_nonneg_left (hrd.trans hd1) hK0]
    · have hdr : d ≤ r := le_of_lt (lt_of_not_ge hrd)
      have ht := htail (mem_Ici.mpr le_rfl) (mem_Ici.mpr hdr) hdr
      have hvd := (hvbasic d hd.le).1
      have hfr := (hsl r (hd.trans_le hdr)).1
      have hfd := (hsl d hd).2.1
      have hinv : 2 / f d ≤ 4 / d := by
        apply (div_le_div_iff₀ (hfpos d hd) hd).mpr
        linarith only [hfhalf]
      have hsmall : 2 * deriv f d / f d ≤ 2 / f d :=
        div_le_div_of_nonneg_right (by linarith only [hfd]) (hfpos d hd).le
      have hlarge : 0 ≤ 2 * deriv f r / f d :=
        div_nonneg (mul_nonneg (by norm_num) hfr) (hfpos d hd).le
      have hds : 4 / d = 8 * (K + 1) := by dsimp only [d]; field_simp; norm_num
      rw [hds] at hinv
      nlinarith [mul_le_mul_of_nonneg_left hd1 hK0]
  by_cases hs : 0 ≤ s
  · exact hp s hs
  · have h := hp (-s) (neg_nonneg.mpr (le_of_not_ge hs))
    rw [show v (-s) = -v s from intrinsicRadialVelocity_odd g hrotation hcomplete s,
      abs_neg] at h
    exact h

end PoincareConjecture.M35.Uniqueness
