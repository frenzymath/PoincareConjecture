import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Variation.Global

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.RicciFlow

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] {J : Set ℝ}

theorem hasDerivAt_integral_volumeMeasure_surface_of_hasDerivAt
    (F : RicciFlow 2 M J) {t : ℝ} (ht : t ∈ interior J)
    {u : ℝ → M → ℝ} {v : M → ℝ}
    (hu : ∀ s ∈ interior J, ∀ y : M,
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => u p.1 p.2) (s, y))
    (hv : ∀ x, HasDerivAt (fun s => u s x) (v x) t) :
    HasDerivAt (fun s => ∫ x, u s x ∂(F.metric s).volumeMeasure)
      (∫ x, v x - (F.connection t).scalarCurvature x * u t x
        ∂(F.metric t).volumeMeasure) t := by
  simpa only [(hv _).deriv] using F.hasDerivAt_integral_volumeMeasure_surface ht hu

end PoincareConjecture.RicciFlow
