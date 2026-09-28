import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric
variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [T3Space M] [T3Space N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]

theorem measurePreserving_volumeMeasure_of_edist_eq
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (e : M ≃ N) (he : ∀ x y, h.edist (e x) (e y) = g.edist x y) :
    MeasurePreserving e g.volumeMeasure h.volumeMeasure := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨⟨h.inner, h.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace N := EMetricSpace.ofRiemannianMetric (𝓡 n) N
  let e' : M ≃ᵢ N := ⟨e, he⟩
  exact e'.measurePreserving_euclideanHausdorffMeasure n

theorem integral_comp_equiv_volumeMeasure
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (e : M ≃ N) (he : ∀ x y, h.edist (e x) (e y) = g.edist x y)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : N → E) :
    (∫ x, F (e x) ∂g.volumeMeasure) = ∫ y, F y ∂h.volumeMeasure := by
  have hp := g.measurePreserving_volumeMeasure_of_edist_eq h e he
  have hp' := h.measurePreserving_volumeMeasure_of_edist_eq g e.symm
    (fun x y => by simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm)
  let em : M ≃ᵐ N := ⟨e, hp.measurable, hp'.measurable⟩
  exact hp.integral_comp em.measurableEmbedding F

end PoincareConjecture.RiemannianMetric
