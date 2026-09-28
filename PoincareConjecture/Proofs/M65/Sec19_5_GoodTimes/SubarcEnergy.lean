import PoincareConjecture.Proofs.M62.Lemma0_4_Continuity
import PoincareConjecture.Proofs.M62.Lemma0_4_Periodicity
import PoincareConjecture.Definitions.M63Ramp
import PoincareConjecture.Proofs.M65.Mathlib.WeightedCauchySchwarz
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic










set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)



theorem m65SubarcCurvature_sq_le (hc : M62ShrinkingCurve F c)
    {t alpha beta : ℝ} (ht : t ∈ Set.Icc a b) (hab : alpha ≤ beta) :
    (m63ArcTotalCurvature F c t alpha beta) ^ 2 ≤
      m63ArcLength F c t alpha beta *
        (∫ x in alpha..beta, m62CurvatureSquared F c t x * curveSpeed F c t x) := by
  have hv : Continuous (curveSpeed F c t) :=
    (M62.speed_continuousOn F c hc).comp_continuous
      (f := fun x : ℝ => (x, t)) (continuous_id.prodMk continuous_const)
      (fun _ => ⟨Set.mem_univ _, ht⟩)
  have hk : Continuous (m62Curvature F c t) :=
    (M62.curvature_continuousOn F c hc).comp_continuous
      (f := fun x : ℝ => (x, t)) (continuous_id.prodMk continuous_const)
      (fun _ => ⟨Set.mem_univ _, ht⟩)
  simpa only [m63ArcTotalCurvature, m63ArcLength, M62.curvature_sq] using
    (intervalIntegral.integral_mul_weight_sq_le hab (M62.speed_nonneg F c t)
      (hv.intervalIntegrable alpha beta) ((hk.mul hv).intervalIntegrable alpha beta)
      (((hk.pow 2).mul hv).intervalIntegrable alpha beta))



theorem m65SubarcEnergy_le (hc : M62ShrinkingCurve F c)
    {t alpha beta : ℝ} (ht : t ∈ Set.Ioo a b)
    (hab : alpha ≤ beta) (hbeta : beta ≤ alpha + curvePeriod) :
    (∫ x in alpha..beta, m62CurvatureSquared F c t x * curveSpeed F c t x) ≤
      ∫ x in (0 : ℝ)..curvePeriod, m62CurvatureSquared F c t x * curveSpeed F c t x := by
  have hclosed := Set.Ioo_subset_Icc_self ht
  have hprod := (M62.curvatureSquared_continuousOn F c hc).mul
    (M62.speed_continuousOn F c hc)
  have hcont : Continuous
      (fun x => m62CurvatureSquared F c t x * curveSpeed F c t x) :=
    hprod.comp_continuous (f := fun x : ℝ => (x, t))
      (continuous_id.prodMk continuous_const) (fun _ => ⟨Set.mem_univ _, hclosed⟩)
  have hper := (M62.curvatureSquared_periodic F c hc ht).mul
    (M62.speed_periodic F c hc hclosed)
  calc
    _ ≤ ∫ x in alpha..alpha + curvePeriod,
        m62CurvatureSquared F c t x * curveSpeed F c t x :=
      intervalIntegral.integral_mono_interval le_rfl hab hbeta
        (Filter.Eventually.of_forall fun x =>
          mul_nonneg (M62.curvatureSquared_nonneg F c t x) (M62.speed_nonneg F c t x))
        (hcont.intervalIntegrable _ _)
    _ = _ := by simpa only [zero_add, Pi.mul_apply] using hper.intervalIntegral_add_eq alpha 0



theorem m65SmallSubarcs_of_energy_le (hc : M62ShrinkingCurve F c)
    {t r delta B : ℝ} (ht : t ∈ Set.Ioo a b) (hr : 0 ≤ r) (hdelta : 0 ≤ delta)
    (henergy : (∫ x in (0 : ℝ)..curvePeriod,
      m62CurvatureSquared F c t x * curveSpeed F c t x) ≤ B)
    (hscale : r * B ≤ delta ^ 2) : M63SmallSubarcs F c t r delta := by
  intro alpha beta hab hbeta hlength
  have he := (m65SubarcEnergy_le F c hc ht hab hbeta).trans henergy
  have he_nonneg : 0 ≤ ∫ x in alpha..beta,
      m62CurvatureSquared F c t x * curveSpeed F c t x :=
    intervalIntegral.integral_nonneg_of_forall hab fun x =>
      mul_nonneg (M62.curvatureSquared_nonneg F c t x) (M62.speed_nonneg F c t x)
  exact le_of_sq_le_sq ((m65SubarcCurvature_sq_le F c hc
    (Set.Ioo_subset_Icc_self ht) hab).trans ((mul_le_mul hlength he he_nonneg hr).trans hscale))
    hdelta

end PoincareConjecture
