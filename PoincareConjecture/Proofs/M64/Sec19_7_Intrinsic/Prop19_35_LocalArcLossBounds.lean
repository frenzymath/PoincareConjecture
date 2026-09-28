import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CurvatureLoss
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_AreaLoss











noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped intervalIntegral

namespace PoincareConjecture




def m64IntrinsicLocalHighCurvatureLength
    (N : IntrinsicAnnulus) (alpha l u : ℝ) : ℝ :=
  ∫ x in Ioo l u ∩
    {x | alpha < intrinsicGeodesicCurvature N.metric N.connection 1 x},
    intrinsicBoundarySpeed N.metric 1 x



theorem m64IntrinsicLocalHighCurvatureLength_nonneg
    (N : IntrinsicAnnulus) (alpha l u : ℝ) :
    0 ≤ m64IntrinsicLocalHighCurvatureLength N alpha l u :=
  integral_nonneg (fun _ => Real.sqrt_nonneg _)




theorem m64Intrinsic_local_high_curvature_length_mul_le_turning
    (N : IntrinsicAnnulus) {alpha l u : ℝ} (hlu : l ≤ u) :
    alpha * m64IntrinsicLocalHighCurvatureLength N alpha l u ≤
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 l u := by
  let speed := intrinsicBoundarySpeed N.metric 1
  let density := fun x => intrinsicGeodesicCurvature N.metric N.connection 1 x * speed x
  let Y := Ioo l u ∩
    {x | alpha < intrinsicGeodesicCurvature N.metric N.connection 1 x}
  have hspeed :=
    (m64Intrinsic_contDiff_boundarySpeed N (by norm_num : (1 : ℝ) ≠ 0)).continuous
  have hdensity :=
    m64Intrinsic_continuous_turning_density N (by norm_num : (1 : ℝ) ≠ 0)
  have hspeedI : IntegrableOn speed (Ioo l u) :=
    hspeed.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hdensityI : IntegrableOn density (Ioo l u) :=
    hdensity.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hY : MeasurableSet Y := measurableSet_Ioo.inter
    (isOpen_lt continuous_const
      (m64Intrinsic_continuous_geodesicCurvature N
        (by norm_num : (1 : ℝ) ≠ 0))).measurableSet
  have hpoint : (∫ x in Y, alpha * speed x) ≤ ∫ x in Y, density x := by
    apply setIntegral_mono_on
      ((hspeedI.mono_set inter_subset_left).const_mul alpha)
      (hdensityI.mono_set inter_subset_left) hY
    intro x hx
    exact mul_le_mul_of_nonneg_right hx.2.le (Real.sqrt_nonneg _)
  have htotal : (∫ x in Y, density x) ≤ ∫ x in Ioo l u, density x := by
    apply setIntegral_mono_set hdensityI
    · exact Eventually.of_forall (fun x =>
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    · exact Eventually.of_forall (fun _ hx => hx.1)
  rw [integral_const_mul] at hpoint
  change alpha * m64IntrinsicLocalHighCurvatureLength N alpha l u ≤ _ at hpoint
  apply hpoint.trans
  calc
    (∫ x in Y, density x) ≤ ∫ x in Ioo l u, density x := htotal
    _ = ∫ x in Ioc l u, density x := setIntegral_congr_set Ioo_ae_eq_Ioc
    _ = intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 l u := by
      rw [intrinsicGeodesicCurvatureIntegral, intervalIntegral.integral_of_le hlu]




theorem m64Intrinsic_local_high_curvature_length_lt_hundredth
    (N : IntrinsicAnnulus) {delta r alpha l u : ℝ}
    (hdelta : 0 < delta) (hr : 0 < r) (hlu : l ≤ u)
    (hlength : intrinsicBoundaryLength N.metric 1 l u = r)
    (hperiod : u ≤ l + rampPeriod) (hturn : N.SmallBoundaryTurning delta r)
    (halpha : 100 * delta / r ≤ alpha) :
    m64IntrinsicLocalHighCurvatureLength N alpha l u < r / 100 := by
  have hturning :
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 l u < delta :=
    hturn l u hlu hperiod (by rw [hlength])
  have hscale := mul_le_mul_of_nonneg_right halpha
    (m64IntrinsicLocalHighCurvatureLength_nonneg N alpha l u)
  have hless :=
    (hscale.trans
      (m64Intrinsic_local_high_curvature_length_mul_le_turning N hlu)).trans_lt hturning
  have hfactor : 0 < 100 * delta / r := by positivity
  have heq : delta = (100 * delta / r) * (r / 100) := by
    field_simp [hr.ne']
  apply (mul_lt_mul_iff_right₀ hfactor).mp
  exact hless.trans_eq heq




theorem m64Intrinsic_local_long_fiber_length_le
    (N : IntrinsicAnnulus) {l u : ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hsub : S ⊆ Icc l u) {height : ℝ → ℝ} (hh : Measurable height)
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (harea : ENNReal.ofReal (c ^ 2) *
      (∫⁻ s in S, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 s) *
        ENNReal.ofReal (height s)) ≤ ENNReal.ofReal (intrinsicAnnulusArea N.metric)) :
    m64IntrinsicLongFiberLength N S height R ≤
      intrinsicAnnulusArea N.metric / (c ^ 2 * R) := by
  let A := S ∩ {s | R ≤ height s}
  let speed := intrinsicBoundarySpeed N.metric 1
  have hA : MeasurableSet A := hS.inter (measurableSet_le measurable_const hh)
  have hspeed :=
    (m64Intrinsic_contDiff_boundarySpeed N (by norm_num : (1 : ℝ) ≠ 0)).continuous
  have hspeedA : IntegrableOn speed A :=
    hspeed.integrableOn_Icc.mono_set (inter_subset_left.trans hsub)
  have hnonneg : 0 ≤ᵐ[volume.restrict A] speed :=
    Eventually.of_forall (fun _ => Real.sqrt_nonneg _)
  have hcut : ENNReal.ofReal R * (∫⁻ s in A, ENNReal.ofReal (speed s)) ≤
      ∫⁻ s in S, ENNReal.ofReal (speed s) * ENNReal.ofReal (height s) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply (setLIntegral_mono' hA (fun s hs => ?_)).trans
      (lintegral_mono_set inter_subset_left)
    rw [mul_comm]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hs.2)
  have hweighted :=
    (mul_le_mul' (le_refl (ENNReal.ofReal (c ^ 2))) hcut).trans harea
  rw [← ofReal_integral_eq_lintegral_ofReal hspeedA hnonneg] at hweighted
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hweighted
  have hAnnulusArea : 0 ≤ intrinsicAnnulusArea N.metric := by
    rw [m64Intrinsic_area_eq_volumeMeasure]
    exact ENNReal.toReal_nonneg
  have hlength : 0 ≤ ∫ s in A, speed s :=
    integral_nonneg (fun _ => Real.sqrt_nonneg _)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg c),
    ENNReal.toReal_ofReal hR.le, ENNReal.toReal_ofReal hlength,
    ENNReal.toReal_ofReal hAnnulusArea] at hreal
  apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hc) hR)).mpr
  change (∫ s in A, speed s) * (c ^ 2 * R) ≤ intrinsicAnnulusArea N.metric
  nlinarith only [hreal]




theorem m64Intrinsic_local_long_fiber_length_lt_tenth
    (N : IntrinsicAnnulus) {l u : ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hsub : S ⊆ Icc l u) {height : ℝ → ℝ} (hh : Measurable height)
    {c R r : ℝ} (hc : 0 < c) (hR : 0 < R) (hr : 0 < r)
    (harea : ENNReal.ofReal (c ^ 2) *
      (∫⁻ s in S, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 s) *
        ENNReal.ofReal (height s)) ≤ ENNReal.ofReal (intrinsicAnnulusArea N.metric))
    (hsmall : intrinsicAnnulusArea N.metric < c ^ 2 * R * (r / 10)) :
    m64IntrinsicLongFiberLength N S height R < r / 10 := by
  have hbound := m64Intrinsic_local_long_fiber_length_le N hS hsub hh hc hR harea
  have hscale : 0 < c ^ 2 * R := mul_pos (sq_pos_of_pos hc) hR
  have hr10 : 0 < r / 10 := div_pos hr (by norm_num)
  have hdiv : intrinsicAnnulusArea N.metric / (c ^ 2 * R) < r / 10 := by
    apply (div_lt_iff₀ hscale).mpr
    nlinarith only [hsmall, hr10]
  exact hbound.trans_lt hdiv

end PoincareConjecture
