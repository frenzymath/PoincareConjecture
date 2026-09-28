import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_StripArea
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryGeometry













noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory

namespace PoincareConjecture




def m64IntrinsicLongFiberLength (N : IntrinsicAnnulus) (S : Set ℝ)
    (height : ℝ → ℝ) (R : ℝ) : ℝ :=
  ∫ s in S ∩ {s | R ≤ height s}, intrinsicBoundarySpeed N.metric 1 s



theorem m64IntrinsicLongFiberLength_nonneg
    (N : IntrinsicAnnulus) (S : Set ℝ) (height : ℝ → ℝ) (R : ℝ) :
    0 ≤ m64IntrinsicLongFiberLength N S height R :=
  integral_nonneg (fun _ => Real.sqrt_nonneg _)




theorem m64Intrinsic_long_fiber_length_le
    (N : IntrinsicAnnulus) {S : Set ℝ} (hS : MeasurableSet S)
    (hsub : S ⊆ Icc (0 : ℝ) rampPeriod) {height : ℝ → ℝ} (hh : Measurable height)
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (harea : ENNReal.ofReal (c ^ 2) *
        (∫⁻ s in S, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 s) *
          ENNReal.ofReal (height s)) ≤ ENNReal.ofReal (intrinsicAnnulusArea N.metric)) :
    m64IntrinsicLongFiberLength N S height R ≤ intrinsicAnnulusArea N.metric / (c ^ 2 * R) := by
  let A := S ∩ {s | R ≤ height s}
  let speed := intrinsicBoundarySpeed N.metric 1
  have hA : MeasurableSet A := hS.inter (measurableSet_le measurable_const hh)
  have hspeed := (m64Intrinsic_contDiff_boundarySpeed N (by norm_num : (1 : ℝ) ≠ 0)).continuous
  have hspeedA : IntegrableOn speed A :=
    hspeed.integrableOn_Icc.mono_set (inter_subset_left.trans hsub)
  have hnonneg : 0 ≤ᵐ[volume.restrict A] speed :=
    Eventually.of_forall (fun _ => Real.sqrt_nonneg _)
  have hcut : ENNReal.ofReal R * (∫⁻ s in A, ENNReal.ofReal (speed s)) ≤
      ∫⁻ s in S, ENNReal.ofReal (speed s) * ENNReal.ofReal (height s) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply (setLIntegral_mono' hA (fun s hs => ?_)).trans (lintegral_mono_set inter_subset_left)
    rw [mul_comm]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hs.2)
  have hweighted := (mul_le_mul' (le_refl (ENNReal.ofReal (c ^ 2))) hcut).trans harea
  rw [← ofReal_integral_eq_lintegral_ofReal hspeedA hnonneg] at hweighted
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hweighted
  have hAnnulusArea : 0 ≤ intrinsicAnnulusArea N.metric := by
    rw [m64Intrinsic_area_eq_volumeMeasure]
    exact ENNReal.toReal_nonneg
  have hlength : 0 ≤ ∫ s in A, speed s := integral_nonneg (fun _ => Real.sqrt_nonneg _)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg c),
    ENNReal.toReal_ofReal hR.le, ENNReal.toReal_ofReal hlength,
    ENNReal.toReal_ofReal hAnnulusArea] at hreal
  apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hc) hR)).mpr
  change (∫ s in A, speed s) * (c ^ 2 * R) ≤ intrinsicAnnulusArea N.metric
  nlinarith only [hreal]




theorem m64Intrinsic_long_fiber_length_lt_tenth
    (N : IntrinsicAnnulus) {S : Set ℝ} (hS : MeasurableSet S)
    (hsub : S ⊆ Icc (0 : ℝ) rampPeriod) {height : ℝ → ℝ} (hh : Measurable height)
    {c R r : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hfirst : r < intrinsicBoundaryLength N.metric 1 0 rampPeriod)
    (harea : ENNReal.ofReal (c ^ 2) *
        (∫⁻ s in S, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 s) *
          ENNReal.ofReal (height s)) ≤ ENNReal.ofReal (intrinsicAnnulusArea N.metric))
    (hsmall : intrinsicAnnulusArea N.metric < c ^ 2 * R * (r / 10)) :
    m64IntrinsicLongFiberLength N S height R <
      intrinsicBoundaryLength N.metric 1 0 rampPeriod / 10 := by
  have hbound := m64Intrinsic_long_fiber_length_le N hS hsub hh hc hR harea
  have hscale : 0 < c ^ 2 * R := mul_pos (sq_pos_of_pos hc) hR
  have hdiv : intrinsicAnnulusArea N.metric / (c ^ 2 * R) < r / 10 := by
    apply (div_lt_iff₀ hscale).mpr
    nlinarith only [hsmall]
  exact (hbound.trans_lt hdiv).trans (by linarith)

end PoincareConjecture
