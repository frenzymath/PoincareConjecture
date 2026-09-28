import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.PullbackCoefficients














set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M30




def WithinBilinearFlowService : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (Fseq : ℕ → RicciFlow n M J)
    (g : ℝ → RiemannianMetric n M),
    UniqueDiffOn ℝ J → RiemannianMetric.IsSmoothFamilyOn g J →
    (∀ (x : M) (r : ℕ) (K : Set (ℝ × EuclideanSpace ℝ (Fin n))),
      IsCompact K → K ⊆ J ×ˢ (extChartAt (𝓡 n) x).target → TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ r
          (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((Fseq k).metric p.1).pullbackCoefficients (extChartAt (𝓡 n) x).symm p.2)
          (J ×ˢ (extChartAt (𝓡 n) x).target))
        (iteratedFDerivWithin ℝ r
          (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
            (g p.1).pullbackCoefficients (extChartAt (𝓡 n) x).symm p.2)
          (J ×ˢ (extChartAt (𝓡 n) x).target)) atTop K) →
      ∃ F : RicciFlow n M J, F.metric = g

end PoincareConjecture.M30
