import PoincareLib.Geometry.RicciFlow.MetricFamily.PullbackCoefficients

/-!
# Explicit supplier for flow realization from included-time bilinear jets

This proposition is the exact interface of the unpublished lower M28
`RicciFlow.exists_of_bilinear_within_spacetime_jets` theorem. It keeps
the actual manifold, metric family and full time-chart derivative domains.
It has no local inhabitant and asserts no new compactness result.

The source is Morgan--Tian Proposition 5.14, pp. 90-91. The pinned lower
statement and publication obligation are recorded in
`proof-work/tasks/M30/derivations/within-bilinear-flow-service.md`.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M30

/-- The unfilled lower supplier for actual Ricci-flow realization from
bilinear within jets, retaining the given total metric family
(Morgan--Tian Proposition 5.14, pp. 90-91). -/
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

end PoincareMT.M30
