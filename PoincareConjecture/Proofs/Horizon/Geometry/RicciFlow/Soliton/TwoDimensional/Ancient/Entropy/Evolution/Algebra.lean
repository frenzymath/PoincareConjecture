import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Functional


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.SurfaceEntropy

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

theorem scalarEntropy_eq_log_integral_sub (D : LeviCivitaData g)
    (hpos : ∀ x, 0 < D.scalarCurvature x) :
    scalarEntropy D =
      (∫ x, D.scalarCurvature x * Real.log (D.scalarCurvature x) ∂g.volumeMeasure) -
      (∫ x, D.scalarCurvature x ∂g.volumeMeasure) * Real.log (meanScalar D) := by
  have hR := D.continuous_scalarCurvature
  have hi := hR.integrable_of_hasCompactSupport (μ := g.volumeMeasure)
    (HasCompactSupport.of_compactSpace _)
  have hiL : Integrable (fun x => D.scalarCurvature x * Real.log (D.scalarCurvature x))
      g.volumeMeasure := (hR.mul (hR.log (fun x => (hpos x).ne'))).integrable_of_hasCompactSupport
    (μ := g.volumeMeasure) (HasCompactSupport.of_compactSpace _)
  rw [scalarEntropy_eq_integral_log_ratio D hpos]
  simp_rw [Real.log_div (hpos _).ne' (meanScalar_pos D hpos).ne', mul_sub]
  rw [integral_sub hiL (hi.mul_const _), integral_mul_const]

theorem integral_scalar_variance_eq (D : LeviCivitaData g) :
    (∫ x, (D.scalarCurvature x - meanScalar D) ^ 2 ∂g.volumeMeasure) =
      (∫ x, (D.scalarCurvature x) ^ 2 ∂g.volumeMeasure) -
      (∫ x, D.scalarCurvature x ∂g.volumeMeasure) * meanScalar D := by
  have hi := D.continuous_scalarCurvature.integrable_of_hasCompactSupport
    (μ := g.volumeMeasure) (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun x => D.scalarCurvature x ^ 2) g.volumeMeasure :=
    (D.continuous_scalarCurvature.pow 2).integrable_of_hasCompactSupport
    (μ := g.volumeMeasure) (HasCompactSupport.of_compactSpace _)
  have hiSub : Integrable (fun x => D.scalarCurvature x ^ 2 -
      2 * D.scalarCurvature x * meanScalar D) g.volumeMeasure :=
    hi2.sub ((hi.const_mul _).mul_const _)
  simp_rw [sub_sq]
  rw [integral_add hiSub (integrable_const _),
    integral_sub hi2 ((hi.const_mul _).mul_const _), integral_mul_const,
    integral_const_mul, integral_const, smul_eq_mul,
    integral_scalarCurvature_eq_meanScalar_mul_volume D]
  ring

end PoincareConjecture.SurfaceEntropy
