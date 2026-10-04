import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.CurveShortening.Integral.Length
import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Closed.IntegralComparison
import PoincareLib.Geometry.CurveShortening.Ramp.Data

/-!
# Length evolution of fixed parameter arcs

The actual speed law gives the length derivative on every fixed ordered
parameter interval. The ambient Ricci bound then gives exponential length
growth through both time endpoints. These are the length inputs in MT2007
Claims 19.59-19.60, pp. 482-484, using the length identity retained by
MT2015Correction Lemma 0.4 and Corollary 19.10, pp. 7-8. See
`2026-09-21-uniform-estimate-fixed-arc-length.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)

/-- A fixed parameter arc has continuous length through the actual time
endpoints. MT2007 Claim 19.59, p. 482; correction Lemma 0.4, pp. 7-8. -/
theorem m63ArcLength_continuousOn (hc : M62ShrinkingCurve F c)
    (alpha beta : ℝ) :
    ContinuousOn (fun t => m63ArcLength F c t alpha beta) (Set.Icc a b) :=
  (speed_continuousOn F c hc).intervalIntegral_prod_left alpha beta

/-- The length derivative on a fixed ordered parameter interval is the
integral of the actual speed derivative. MT2007 Claims 19.59-19.60,
pp. 482-484; correction Lemma 0.4, pp. 7-8. -/
theorem m63ArcLength_hasDerivAt (hc : M62ShrinkingCurve F c)
    {alpha beta : ℝ} (hab : alpha ≤ beta)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    HasDerivAt (fun s => m63ArcLength F c s alpha beta)
      (-(∫ x in alpha..beta,
        (m62CurvatureSquared F c t x + m62TangentRicci F c t x) *
          curveSpeed F c t x)) t := by
  obtain rfl | hab := hab.eq_or_lt
  · simpa only [m63ArcLength, intervalIntegral.integral_same, neg_zero] using
      (hasDerivAt_const t (0 : ℝ))
  let V := fun z : ℝ × ℝ => curveSpeed F c z.2 z.1
  have hV : ContDiffOn ℝ ∞ V (Set.Icc alpha beta ×ˢ Set.Ioo a b) :=
    (speed_joint_contDiffOn F c hc).mono
      (Set.prod_mono (Set.subset_univ _) Set.Subset.rfl)
  have hd := M08.hasDerivAt_variationIntegral hab isOpen_Ioo V hV ht
  apply hd.congr_deriv
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Set.Icc alpha beta := by
    simpa only [Set.uIcc_of_le hab.le] using hx
  have heq := (M08.hasDerivAt_variationParameter isOpen_Ioo V hV hx' ht).unique
    (hasDerivAt_speed F c hc ht x)
  dsimp only
  rw [heq]
  ring

/-- The Ricci bound controls the fixed-arc length derivative while retaining
the negative curvature energy. MT2007 Claim 19.59, p. 482; correction
Lemma 0.4, pp. 7-8. -/
theorem m63ArcLength_deriv_le_integral (hc : M62ShrinkingCurve F c)
    {K0 K1 K2 : ℝ} (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {alpha beta : ℝ} (hab : alpha ≤ beta)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    deriv (fun s => m63ArcLength F c s alpha beta) t ≤ ∫ x in alpha..beta,
      (K2 - m62CurvatureSquared F c t x) * curveSpeed F c t x := by
  have hclosed := Set.Ioo_subset_Icc_self ht
  have hV : Continuous (curveSpeed F c t) :=
    (speed_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨Set.mem_univ _, hclosed⟩)
  have hK : Continuous (m62CurvatureSquared F c t) :=
    (curvatureSquared_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨Set.mem_univ _, hclosed⟩)
  rw [(m63ArcLength_hasDerivAt F c hc hab ht).deriv, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_mono hab
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

/-- Dropping nonnegative curvature energy bounds the growth of every fixed
ordered parameter arc. MT2007 Claim 19.59, p. 482; corrected Corollary
19.10, MT2015Correction p. 8. -/
theorem m63ArcLength_deriv_le (hc : M62ShrinkingCurve F c)
    {K0 K1 K2 : ℝ} (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {alpha beta : ℝ} (hab : alpha ≤ beta)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    deriv (fun s => m63ArcLength F c s alpha beta) t ≤
      K2 * m63ArcLength F c t alpha beta := by
  have hclosed := Set.Ioo_subset_Icc_self ht
  have hV : Continuous (curveSpeed F c t) :=
    (speed_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨Set.mem_univ _, hclosed⟩)
  have hK : Continuous (m62CurvatureSquared F c t) :=
    (curvatureSquared_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨Set.mem_univ _, hclosed⟩)
  calc
    deriv (fun s => m63ArcLength F c s alpha beta) t ≤ ∫ x in alpha..beta,
        (K2 - m62CurvatureSquared F c t x) * curveSpeed F c t x :=
      m63ArcLength_deriv_le_integral F c hc hBounds hab ht
    _ ≤ ∫ x in alpha..beta, K2 * curveSpeed F c t x := by
      apply intervalIntegral.integral_mono hab
        (((continuous_const.sub hK).mul hV).intervalIntegrable _ _)
        ((hV.const_mul K2).intervalIntegrable _ _)
      intro x
      exact mul_le_mul_of_nonneg_right
        (sub_le_self _ (curvatureSquared_nonneg F c t x)) (speed_nonneg F c t x)
    _ = K2 * m63ArcLength F c t alpha beta := intervalIntegral.integral_const_mul _ _

/-- Fixed-label arc length obeys the ambient exponential upper bound at
all included times, without endpoint differentiation. MT2007 Claim 19.59,
p. 482; corrected Corollary 19.10, MT2015Correction p. 8. -/
theorem m63ArcLength_le_mul_exp (hc : M62ShrinkingCurve F c)
    {K0 K1 K2 : ℝ} (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {alpha beta : ℝ} (hab : alpha ≤ beta)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t) :
    m63ArcLength F c t alpha beta ≤
      m63ArcLength F c s alpha beta * Real.exp (K2 * (t - s)) :=
  Poincare.Parabolic.le_mul_exp_of_hasDerivAt_le_mul
    (m63ArcLength_continuousOn F c hc alpha beta)
    (fun _ hr => (m63ArcLength_hasDerivAt F c hc hab hr).differentiableAt.hasDerivAt)
    (fun _ hr => m63ArcLength_deriv_le F c hc hBounds hab hr) hs ht hst

end PoincareMT
