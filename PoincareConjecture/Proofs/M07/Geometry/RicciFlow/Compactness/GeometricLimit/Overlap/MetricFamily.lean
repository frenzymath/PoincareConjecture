import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.Descent
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Gluing.Construction



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology Bundle PoincareConjecture
open scoped Manifold ContDiff
noncomputable section
namespace Poincare.Gluing
variable {n : ℕ}

variable {A : Type*} (U : A → Set (EuclideanSpace ℝ (Fin n)))
    (hU : ∀ i, IsOpen (U i)) [∀ i, Nonempty (Piece U i)]



theorem quotientMetric_isSmoothFamilyOn
    (O : OverlapSystem (fun i => Piece U i)) (hs : SmoothOverlap U hU O)
    (g : ∀ i, ℝ → CanonicalMetric U hU i) {J : Set ℝ}
    (hg : ∀ i,
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI : IsManifold (𝓡 n) ∞ (Piece U i) :=
        (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
      RiemannianMetric.IsSmoothFamilyOn (g i) J)
    (hcompat : ∀ t, CompatibleMetrics U hU O (fun i => g i t)) :
    letI := quotientChartedSpace U hU O
    letI := quotient_isManifold U hU O hs
    RiemannianMetric.IsSmoothFamilyOn
      (fun t => quotientMetric U hU O hs (fun i => g i t) (hcompat t)) J := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hs
  refine isSmoothFamilyOn_of_local_diffeomorphisms g _ hg O.include
    (include_isLocalDiffeomorph U hU O hs) ?_ ?_
  · intro y
    have hy : y ∈ ⋃ i, Set.range (O.include i) := by rw [O.include_cover]; trivial
    simpa only [mem_iUnion, mem_range] using hy
  · intro t _ i
    exact quotientMetric_preserves U hU O hs (fun i => g i t) (hcompat t) i

end Poincare.Gluing
