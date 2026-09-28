import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Positivity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Measure
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.SurfaceEntropy

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] {g : RiemannianMetric 2 M}

noncomputable def meanScalar (D : LeviCivitaData g) : ℝ :=
  (∫ x, D.scalarCurvature x ∂g.volumeMeasure) / g.volumeMeasure.real Set.univ

noncomputable def scalarEntropy (D : LeviCivitaData g) : ℝ :=
  ∫ x, relativeDensity (meanScalar D) (D.scalarCurvature x) ∂g.volumeMeasure

theorem volumeMeasure_rescaled_surface (c : ℝ) (hc : 0 < c) :
    (rescaledMetric g c hc).volumeMeasure = ENNReal.ofReal c • g.volumeMeasure := by
  rw [rescaledMetric_volumeMeasure, ← ENNReal.ofReal_pow (Real.sqrt_nonneg c),
    Real.sq_sqrt hc.le]

theorem meanScalar_rescaled (D : LeviCivitaData g) (c : ℝ) (hc : 0 < c) :
    meanScalar (rescaledMetric_connection g D c hc) = c⁻¹ * meanScalar D := by
  unfold meanScalar
  rw [volumeMeasure_rescaled_surface c hc]
  simp only [rescaledMetric_scalarCurvature, integral_smul_measure, integral_const_mul,
    ENNReal.toReal_ofReal hc.le, smul_eq_mul, Measure.real, Measure.smul_apply,
    ENNReal.toReal_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] in
theorem relativeDensity_mul (a r x : ℝ) (ha : a ≠ 0) :
    relativeDensity (a * r) (a * x) = a * relativeDensity r x := by
  unfold relativeDensity
  rw [mul_div_mul_left _ _ ha]
  ring

theorem scalarEntropy_rescaled (D : LeviCivitaData g) (c : ℝ) (hc : 0 < c) :
    scalarEntropy (rescaledMetric_connection g D c hc) = scalarEntropy D := by
  unfold scalarEntropy
  rw [meanScalar_rescaled, volumeMeasure_rescaled_surface c hc]
  simp only [rescaledMetric_scalarCurvature,
    relativeDensity_mul c⁻¹ _ _ (inv_ne_zero hc.ne'), integral_smul_measure,
    integral_const_mul, ENNReal.toReal_ofReal hc.le, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

section Compact

variable [CompactSpace M] [Nonempty M]

theorem volume_pos : 0 < g.volumeMeasure.real Set.univ := by
  let : g.volumeMeasure.IsOpenPosMeasure := g.volumeMeasure_isOpenPosMeasure
  exact ENNReal.toReal_pos (ne_of_gt (isOpen_univ.measure_pos _ Set.univ_nonempty))
    (measure_ne_top _ _)

theorem integral_scalarCurvature_eq_meanScalar_mul_volume (D : LeviCivitaData g) :
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) =
      meanScalar D * g.volumeMeasure.real Set.univ := by
  rw [meanScalar, div_mul_cancel₀ _ (ne_of_gt (volume_pos (g := g)))]

theorem meanScalar_pos (D : LeviCivitaData g)
    (hpos : ∀ x, 0 < D.scalarCurvature x) : 0 < meanScalar D := by
  let : g.volumeMeasure.IsOpenPosMeasure := g.volumeMeasure_isOpenPosMeasure
  have hi := D.continuous_scalarCurvature.integrable_of_hasCompactSupport
    (μ := g.volumeMeasure) (HasCompactSupport.of_compactSpace _)
  exact div_pos (integral_pos_of_integrable_nonneg_nonzero
    D.continuous_scalarCurvature hi (fun x => (hpos x).le)
    (ne_of_gt (hpos (Classical.arbitrary M)))) (volume_pos (g := g))

theorem meanScalar_of_constant (D : LeviCivitaData g) {r : ℝ}
    (hR : ∀ x, D.scalarCurvature x = r) : meanScalar D = r := by
  unfold meanScalar
  simp only [hR, integral_const, smul_eq_mul]
  exact mul_div_cancel_left₀ _ (ne_of_gt (volume_pos (g := g)))

theorem scalarEntropy_of_constant (D : LeviCivitaData g) {r : ℝ}
    (hR : ∀ x, D.scalarCurvature x = r) : scalarEntropy D = 0 := by
  unfold scalarEntropy
  rw [meanScalar_of_constant D hR]
  by_cases hr : r = 0
  · simp [hR, hr, relativeDensity]
  · simp [hR, relativeDensity, hr]

theorem scalarEntropy_nonneg (D : LeviCivitaData g)
    (hpos : ∀ x, 0 < D.scalarCurvature x) : 0 ≤ scalarEntropy D :=
  integral_relativeDensity_nonneg g (meanScalar_pos D hpos) hpos

theorem scalarEntropy_eq_zero_iff (D : LeviCivitaData g)
    (hpos : ∀ x, 0 < D.scalarCurvature x) :
    scalarEntropy D = 0 ↔ ∀ x, D.scalarCurvature x = meanScalar D :=
  integral_relativeDensity_eq_zero_iff g D.continuous_scalarCurvature
    (meanScalar_pos D hpos) hpos

theorem scalarEntropy_eq_integral_log_ratio (D : LeviCivitaData g)
    (hpos : ∀ x, 0 < D.scalarCurvature x) :
    scalarEntropy D = ∫ x, D.scalarCurvature x *
      Real.log (D.scalarCurvature x / meanScalar D) ∂g.volumeMeasure := by
  have hR := D.continuous_scalarCurvature
  have hr := meanScalar_pos D hpos
  have hlog := (hR.div_const (meanScalar D)).log
    (fun x => ne_of_gt (div_pos (hpos x) hr))
  have hiR := hR.integrable_of_hasCompactSupport
    (μ := g.volumeMeasure) (HasCompactSupport.of_compactSpace _)
  have hiL : Integrable (fun x => D.scalarCurvature x *
      Real.log (D.scalarCurvature x / meanScalar D)) g.volumeMeasure :=
    (hR.mul hlog).integrable_of_hasCompactSupport
    (μ := g.volumeMeasure) (HasCompactSupport.of_compactSpace _)
  have hiSub : Integrable (fun x => D.scalarCurvature x *
      Real.log (D.scalarCurvature x / meanScalar D) - D.scalarCurvature x)
      g.volumeMeasure := hiL.sub hiR
  unfold scalarEntropy relativeDensity
  rw [integral_add hiSub (integrable_const (meanScalar D)),
    integral_sub hiL hiR,
    integral_const, smul_eq_mul, integral_scalarCurvature_eq_meanScalar_mul_volume D]
  ring

end Compact

end PoincareConjecture.SurfaceEntropy
