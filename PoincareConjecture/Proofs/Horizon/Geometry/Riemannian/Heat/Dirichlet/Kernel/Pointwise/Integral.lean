import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise







set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}

theorem continuous_heatKernelContinuous_row (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) (t : ℝ) (ht : 0 < t) (x : M) :
    Continuous (heatKernelContinuous D S t ht x) := by
  simpa only [Function.comp_def, id_eq] using
    (continuous_heatKernelContinuous D S t ht).comp
      (continuous_const.prodMk (continuous_id : Continuous (id : M → M)))

theorem integrable_heatKernelContinuous (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) (t : ℝ) (ht : 0 < t) (x : M) :
    Integrable (heatKernelContinuous D S t ht x) (g.volumeMeasure.restrict Ω) :=
  ((continuous_heatKernelContinuous_row D S t ht x).continuousOn.integrableOn_compact
    S.isCompact_closure).mono_set subset_closure

theorem integrable_heatKernelContinuous_mul_of_continuousOn (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) (t : ℝ) (ht : 0 < t) (x : M)
    {φ : M → ℝ} (hφ : ContinuousOn φ (closure Ω)) :
    Integrable (fun y => heatKernelContinuous D S t ht x y * φ y)
      (g.volumeMeasure.restrict Ω) :=
  (((continuous_heatKernelContinuous_row D S t ht x).continuousOn.mul hφ).integrableOn_compact
    S.isCompact_closure).mono_set subset_closure

end PoincareConjecture.LeviCivitaData.Dirichlet
