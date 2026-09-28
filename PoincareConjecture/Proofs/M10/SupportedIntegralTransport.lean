import PoincareConjecture.Proofs.M10.ChartIntegralTransport








set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M]


theorem supported_calibrated_integral_transport (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    (hρ : ContinuousOn (pullbackJacobian g e) e.source)
    {f : M → ℝ} {a : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : AEStronglyMeasurable f (calibratedMetricVolume g))
    (hfzero : ∀ q ∉ e.target, f q = 0) (ha : Integrable a volume)
    (hazero : ∀ y ∉ e.source, a y = 0)
    (heq : ∀ y ∈ e.source, pullbackJacobian g e y * f (e y) = a y) :
    Integrable f (calibratedMetricVolume g) ∧
      (∫ q, f q ∂calibratedMetricVolume g) = ∫ y, a y := by
  have heqae : (fun y ↦ pullbackJacobian g e y * f (e y)) =ᵐ[volume.restrict e.source] a :=
    (ae_restrict_iff' e.open_source.measurableSet).mpr (Eventually.of_forall heq)
  have hfi : IntegrableOn f e.target (calibratedMetricVolume g) :=
    (integrableOn_calibrated_iff_pullback g e he hei hρ hf.restrict).mpr
      (ha.integrableOn.congr heqae.symm)
  refine ⟨hfi.integrable_of_forall_notMem_eq_zero hfzero, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hfzero,
    integralOn_calibrated_eq_pullback g e he hei hρ hf.restrict]
  exact (integral_congr_ae heqae).trans
    (setIntegral_eq_integral_of_forall_compl_eq_zero hazero)

end PoincareConjecture.M10
