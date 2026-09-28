import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.Coverage
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.CutLocus

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal Manifold ContDiff Topology

namespace Poincare.VolumeComparison

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem volumeMeasure_ball_eq_image_sdiff_terminal
    (g : PoincareConjecture.RiemannianMetric n M) (p : M)
    {e : EuclideanSpace ℝ (Fin n) → M} {R r : ℝ}
    (hcover : e '' localMinimizingSet (fun v => g.edist p (e v)) R = g.ball p R)
    (hnull : g.volumeMeasure (e '' terminalRadialPoints
      (localMinimizingSet (fun v => g.edist p (e v)) R) R) = 0)
    (hr : 0 < r) (hrR : r ≤ R) :
    g.volumeMeasure (g.ball p r) =
      g.volumeMeasure (e '' ((localMinimizingSet (fun v => g.edist p (e v)) R \
        terminalRadialPoints (localMinimizingSet (fun v => g.edist p (e v)) R) R) ∩
          Metric.ball 0 r)) := by
  let S := localMinimizingSet (fun v => g.edist p (e v)) R
  let T := terminalRadialPoints S R
  have himage := image_localMinimizingSet_inter_ball g p hcover hr hrR
  change e '' (S ∩ Metric.ball 0 r) = g.ball p r at himage
  change g.volumeMeasure (g.ball p r) =
    g.volumeMeasure (e '' ((S \ T) ∩ Metric.ball 0 r))
  rw [← himage]
  apply le_antisymm
  · calc
      g.volumeMeasure (e '' (S ∩ Metric.ball 0 r)) ≤
          g.volumeMeasure ((e '' ((S \ T) ∩ Metric.ball 0 r)) ∪ e '' T) := by
        apply measure_mono
        rintro x ⟨v, ⟨hvS, hvr⟩, rfl⟩
        by_cases hvT : v ∈ T
        · exact Or.inr ⟨v, hvT, rfl⟩
        · exact Or.inl ⟨v, ⟨⟨hvS, hvT⟩, hvr⟩, rfl⟩
      _ ≤ g.volumeMeasure (e '' ((S \ T) ∩ Metric.ball 0 r)) +
          g.volumeMeasure (e '' T) := measure_union_le _ _
      _ = g.volumeMeasure (e '' ((S \ T) ∩ Metric.ball 0 r)) := by
        rw [show g.volumeMeasure (e '' T) = 0 from hnull, add_zero]
  · apply measure_mono
    exact Set.image_mono fun _ hv => ⟨hv.1.1, hv.2⟩

end Poincare.VolumeComparison
