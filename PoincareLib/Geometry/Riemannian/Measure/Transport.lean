import PoincareLib.Geometry.Riemannian.Measure.Basic

/-!
# Volume in global arclength coordinates

A distance-preserving global coordinate on a one-dimensional manifold carries
the retained volume to Lebesgue measure. This is the measure-transport step for
the real Gaussian model; existence of global arclength coordinates is separate.

Reference: Chow et al., Part III, Proposition 26.49, equation (26.132),
printed p. 378.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.RiemannianMetric

variable {M : Type u} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
  [IsManifold (𝓡 1) ∞ M]

/-- A global intrinsic isometry to the line preserves the normalized volume.
No independent volume-preservation assumption is needed for arclength transport. -/
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

end PoincareMT.RiemannianMetric
