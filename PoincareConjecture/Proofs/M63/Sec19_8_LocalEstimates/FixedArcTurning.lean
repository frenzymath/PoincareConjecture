import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FixedArcLength
import PoincareConjecture.Proofs.M62.Lemma0_4_Periodicity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic











set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)



theorem m63ArcTotalCurvature_continuousOn (hc : M62ShrinkingCurve F c)
    (alpha beta : ℝ) :
    ContinuousOn (fun t => m63ArcTotalCurvature F c t alpha beta) (Set.Icc a b) :=
  ((curvature_continuousOn F c hc).mul
    (speed_continuousOn F c hc)).intervalIntegral_prod_left alpha beta



theorem m63ArcTotalCurvature_nonneg {alpha beta : ℝ}
    (hab : alpha ≤ beta) (t : ℝ) :
    0 ≤ m63ArcTotalCurvature F c t alpha beta :=
  intervalIntegral.integral_nonneg_of_forall hab fun x =>
    mul_nonneg (curvature_nonneg F c t x) (speed_nonneg F c t x)



theorem m63ArcLength_le_length (hc : M62ShrinkingCurve F c)
    {alpha beta : ℝ} (hab : alpha ≤ beta)
    (hperiod : beta ≤ alpha + curvePeriod)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    m63ArcLength F c t alpha beta ≤ m62Length F c t := by
  have hV : Continuous (curveSpeed F c t) :=
    (speed_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨Set.mem_univ _, ht⟩)
  calc
    _ ≤ ∫ x in alpha..alpha + curvePeriod, curveSpeed F c t x :=
      intervalIntegral.integral_mono_interval le_rfl hab hperiod
        (Filter.Eventually.of_forall (speed_nonneg F c t)) (hV.intervalIntegrable _ _)
    _ = m62Length F c t := by
      simpa only [zero_add, m62Length] using
        (speed_periodic F c hc ht).intervalIntegral_add_eq alpha 0




theorem m63ArcTotalCurvature_le_total (hc : M62ShrinkingCurve F c)
    {alpha beta : ℝ} (hab : alpha ≤ beta)
    (hperiod : beta ≤ alpha + curvePeriod)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    m63ArcTotalCurvature F c t alpha beta ≤ m62TotalCurvature F c t := by
  have hinter (s : ℝ) (hs : s ∈ Set.Ioo a b) :
      m63ArcTotalCurvature F c s alpha beta ≤ m62TotalCurvature F c s := by
    let d : ℝ → ℝ := fun x => m62Curvature F c s x * curveSpeed F c s x
    have hcont : Continuous d :=
      ((curvature_continuousOn F c hc).mul
        (speed_continuousOn F c hc)).comp_continuous
          (continuous_id.prodMk continuous_const)
          (fun _ => ⟨Set.mem_univ _, Set.Ioo_subset_Icc_self hs⟩)
    have hnonneg (x : ℝ) : 0 ≤ d x :=
      mul_nonneg (curvature_nonneg F c s x) (speed_nonneg F c s x)
    have hper : Function.Periodic d curvePeriod := by
      intro x
      dsimp only [d, m62Curvature]
      rw [curvatureSquared_periodic F c hc hs x,
        speed_periodic F c hc (Set.Ioo_subset_Icc_self hs) x]
    calc
      _ ≤ ∫ x in alpha..alpha + curvePeriod, d x :=
        intervalIntegral.integral_mono_interval le_rfl hab hperiod
          (Filter.Eventually.of_forall hnonneg) (hcont.intervalIntegrable _ _)
      _ = m62TotalCurvature F c s := by
        simpa only [zero_add, m62TotalCurvature, d] using
          hper.intervalIntegral_add_eq alpha 0
  have htime : a < b := by
    obtain ⟨s, hs, r, hr, hne⟩ := F.nontrivial
    by_contra! h
    exact hne (by linarith [hs.1, hs.2, hr.1, hr.2])
  apply le_on_closure hinter
  · simpa only [closure_Ioo htime.ne] using
      m63ArcTotalCurvature_continuousOn F c hc alpha beta
  · simpa only [closure_Ioo htime.ne] using total_curvature_continuous F c hc
  · simpa only [closure_Ioo htime.ne] using ht

end PoincareConjecture
