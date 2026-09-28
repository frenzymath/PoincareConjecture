import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Basic

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RiemannianMetric

variable {M : Type u} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
  [IsManifold (𝓡 1) ∞ M]

theorem measurePreserving_volumeMeasure_real (g : RiemannianMetric 1 M)
    (e : M ≃ ℝ) (he : ∀ x y, EDist.edist (e x) (e y) = g.edist x y) :
    MeasurePreserving e (volumeMeasure g) volume := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 1) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 1))
      (TangentSpace (𝓡 1) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 1) M
  let e' : M ≃ᵢ ℝ := ⟨e, he⟩
  have hvol : (Measure.euclideanHausdorffMeasure 1 : Measure ℝ) = volume := by
    simpa using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ))
  change MeasurePreserving e' (Measure.euclideanHausdorffMeasure 1) volume
  rw [← hvol]
  exact e'.measurePreserving_euclideanHausdorffMeasure 1

end PoincareConjecture.RiemannianMetric
