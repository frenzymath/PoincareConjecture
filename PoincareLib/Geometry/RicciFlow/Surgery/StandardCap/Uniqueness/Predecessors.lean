import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Local.Theory
import PoincareLib.Geometry.RicciFlow.Curvature.Theory
import PoincareLib.Geometry.RicciFlow.Compactness.Convergence
import PoincareLib.Geometry.RicciFlow.Rescaling.Theory
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Statement
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Theory

/-!
# Earlier services for M35's standard-flow estimates

All direct carriers are Type 0. M04, compact surface uniqueness and M07
support geometry of an arbitrary competing flow; M13 supplies actual
rescaling and metric transport; M27 and M30 supply the blowup arguments.
The supplied M34 existence package remains the geometric input. See the
complete derivation in reviews/contracts/2026-09-17-m35-full-contract.md.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT

structure M35StandardCapPredecessors : Prop where
  curvature : RicciFlowCurvatureTheory.{0}
  compact_surface_uniqueness :
    ∀ (M : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
      [T2Space M] [SecondCountableTopology M] [CompactSpace M],
      RicciFlowUniqueness 2 M
  pointed_compactness :
    ∀ {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses 3 T' T),
      Nonempty (PointedRicciFlowCompactnessConclusion H)
  ordinary_flow : ∀ (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    (I : SpacetimeInterval) (F : RicciFlow 3 M I.domain) (Q : ℝ) (hQ : 0 < Q) (a : ℝ),
    Nonempty (OrdinaryParabolicRescaling F Q hQ a)
  metric_homothety : ∀ (M N : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N]
    [T3Space M] [MeasurableSpace M] [BorelSpace M]
    [T3Space N] [MeasurableSpace N] [BorelSpace N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (f : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (Q : ℝ), 0 < Q →
    MetricHomothety g h f Q → MetricHomothetyCalculus g h f Q
  kappa_models : RepairedKappaAlternativeTheory.{0}
  long_limits : ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 400 ∧
    M30LongLimitStatement.{0} epsilon₀

end PoincareMT
