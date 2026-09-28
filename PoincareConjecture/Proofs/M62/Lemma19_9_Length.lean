import PoincareConjecture.Proofs.M62.Lemma0_1_SpeedEvolution
import PoincareConjecture.Proofs.M62.Lemma0_4_Continuity
import PoincareConjecture.Proofs.M08.VariationIntegral
import PoincareConjecture.Statements.Ch19.CurveEvolution

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)

theorem length_density_continuous (hc : M62ShrinkingCurve F c)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    Continuous (fun x ↦
      (m62CurvatureSquared F c t x + m62TangentRicci F c t x) *
        curveSpeed F c t x) := by
  let V := fun z : ℝ × ℝ ↦ curveSpeed F c z.2 z.1
  have hV := speed_joint_contDiffOn F c hc
  have hpartial := M08.variationParameterDeriv_contDiffOn
    (uniqueDiffOn_univ : UniqueDiffOn ℝ (Set.univ : Set ℝ)) isOpen_Ioo V hV
  have hslice : Continuous (fun x ↦
      M08.variationParameterDeriv Set.univ (Set.Ioo a b) V (x, t)) :=
    hpartial.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ ↦ ⟨Set.mem_univ _, ht⟩)
  have heq (x : ℝ) := (M08.hasDerivAt_variationParameter isOpen_Ioo V hV
    (Set.mem_univ x) ht).unique (hasDerivAt_speed F c hc ht x)
  convert hslice.neg using 1
  funext x
  change (m62CurvatureSquared F c t x + m62TangentRicci F c t x) *
    curveSpeed F c t x = -M08.variationParameterDeriv Set.univ (Set.Ioo a b) V (x, t)
  rw [heq x]
  ring

theorem hasDerivAt_length (hc : M62ShrinkingCurve F c)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    HasDerivAt (m62Length F c)
      (-(∫ x in (0 : ℝ)..curvePeriod,
        (m62CurvatureSquared F c t x + m62TangentRicci F c t x) *
          curveSpeed F c t x)) t := by
  have hperiod : 0 < curvePeriod := by
    unfold curvePeriod
    positivity
  let V := fun z : ℝ × ℝ ↦ curveSpeed F c z.2 z.1
  have hV : ContDiffOn ℝ ∞ V (Set.Icc 0 curvePeriod ×ˢ Set.Ioo a b) :=
    (speed_joint_contDiffOn F c hc).mono
      (Set.prod_mono (Set.subset_univ _) Set.Subset.rfl)
  have hd := M08.hasDerivAt_variationIntegral hperiod isOpen_Ioo V hV ht
  apply hd.congr_deriv
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Set.Icc 0 curvePeriod := by
    simpa only [Set.uIcc_of_le hperiod.le] using hx
  have heq := (M08.hasDerivAt_variationParameter isOpen_Ioo V hV hx' ht).unique
    (hasDerivAt_speed F c hc ht x)
  dsimp only
  rw [heq]
  ring

theorem length_deriv_le_integral (hc : M62ShrinkingCurve F c)
    {K0 K1 K2 : ℝ} (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    deriv (m62Length F c) t ≤ ∫ x in (0 : ℝ)..curvePeriod,
      (K2 - m62CurvatureSquared F c t x) * curveSpeed F c t x := by
  have hclosed := Set.Ioo_subset_Icc_self ht
  have hperiod : 0 ≤ curvePeriod := by
    unfold curvePeriod
    positivity
  have hV : Continuous (curveSpeed F c t) :=
    (speed_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ ↦ ⟨Set.mem_univ _, hclosed⟩)
  have hK : Continuous (m62CurvatureSquared F c t) :=
    (curvatureSquared_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ ↦ ⟨Set.mem_univ _, hclosed⟩)
  rw [(hasDerivAt_length F c hc ht).deriv, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_mono hperiod
    ((length_density_continuous F c hc ht).neg.intervalIntegrable _ _)
    (((continuous_const.sub hK).mul hV).intervalIntegrable _ _)
  intro x
  have hunit := (unitTangent_norm F c hc hclosed x).le
  have hRic : -K2 ≤ m62TangentRicci F c t x :=
    (abs_le.mp (hBounds.ricci t hclosed (c x t)
      (spatialUnitTangent F c t x) (spatialUnitTangent F c t x) hunit hunit)).1
  calc
    -((m62CurvatureSquared F c t x + m62TangentRicci F c t x) *
        curveSpeed F c t x) =
      (-m62CurvatureSquared F c t x - m62TangentRicci F c t x) *
        curveSpeed F c t x := by ring
    _ ≤ (K2 - m62CurvatureSquared F c t x) * curveSpeed F c t x :=
      mul_le_mul_of_nonneg_right (by linarith) (speed_nonneg F c t x)

theorem length_deriv_le (hc : M62ShrinkingCurve F c)
    {K0 K1 K2 : ℝ} (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    deriv (m62Length F c) t ≤ K2 * m62Length F c t := by
  have hclosed := Set.Ioo_subset_Icc_self ht
  have hperiod : 0 ≤ curvePeriod := by
    unfold curvePeriod
    positivity
  have hV : Continuous (curveSpeed F c t) :=
    (speed_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ ↦ ⟨Set.mem_univ _, hclosed⟩)
  have hK : Continuous (m62CurvatureSquared F c t) :=
    (curvatureSquared_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ ↦ ⟨Set.mem_univ _, hclosed⟩)
  calc
    deriv (m62Length F c) t ≤ ∫ x in (0 : ℝ)..curvePeriod,
        (K2 - m62CurvatureSquared F c t x) * curveSpeed F c t x :=
      length_deriv_le_integral F c hc hBounds ht
    _ ≤ ∫ x in (0 : ℝ)..curvePeriod, K2 * curveSpeed F c t x := by
      apply intervalIntegral.integral_mono hperiod
        (((continuous_const.sub hK).mul hV).intervalIntegrable _ _)
        ((hV.const_mul K2).intervalIntegrable _ _)
      intro x
      exact mul_le_mul_of_nonneg_right
        (sub_le_self _ (curvatureSquared_nonneg F c t x)) (speed_nonneg F c t x)
    _ = K2 * m62Length F c t := intervalIntegral.integral_const_mul _ _

end PoincareConjecture.M62
