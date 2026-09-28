import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.FiniteCompactness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Reselect
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Relative.Pointed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientRescalingSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space PointedGeometricConvergence.carrierPreconnected

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

noncomputable abbrev windowCompactnessHypotheses
    (S : AncientRescalingSequence K) (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ) :=
  S.smallCompactnessHypotheses j (S.compactnessWindow_curvature_bound P j)

abbrev FiniteWindowLimit (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ) :=
  PointedRicciFlowCompactnessConclusion (S.windowCompactnessHypotheses P j)

structure WindowExtension (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ) (G : S.FiniteWindowLimit P j) where
  next : S.FiniteWindowLimit P (j + 1)
  refinement : ℕ → ℕ
  refinement_strictMono : StrictMono refinement
  subsequence_eq : next.geometric_limit.subsequence = G.geometric_limit.subsequence ∘ refinement
  equiv : Diffeomorph (𝓡 n) (𝓡 n) G.geometric_limit.limitCarrier.carrier
    next.geometric_limit.limitCarrier.carrier ∞
  base_eq : equiv G.geometric_limit.limitFlow.base = next.geometric_limit.limitFlow.base
  metric_inner_eq : ∀ t,
    t ∈ Ioo (compactnessLower j + 1) (compactnessUpper j + 1) →
    t ∈ Ioo (compactnessLower (j + 1) + 1) (compactnessUpper (j + 1) + 1) →
    ∀ x (v w : TangentSpace (𝓡 n) x),
      (next.geometric_limit.limitFlow.metricAt t).inner (equiv x)
        (mfderiv (𝓡 n) (𝓡 n) equiv x v) (mfderiv (𝓡 n) (𝓡 n) equiv x w) =
      (G.geometric_limit.limitFlow.metricAt t).inner x v w

theorem exists_windowExtension (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ) (Q : S.FiniteWindowLimit P j) :
    Nonempty (S.WindowExtension P j Q) := by
  let H := (S.windowCompactnessHypotheses P (j + 1)).subsequence
    Q.geometric_limit.subsequence Q.geometric_limit.subsequence_strictMono
  obtain ⟨R⟩ := P.pointed_compactness H.time_bounds.1 H.time_bounds.2 H
  let G := Q.geometric_limit.reselect R.geometric_limit.subsequence
    R.geometric_limit.subsequence_strictMono
  let L := R.geometric_limit.ofSubsequence Q.geometric_limit.subsequence_strictMono
  have hGtime := (S.windowCompactnessHypotheses P j).time_bounds
  have hLtime := (S.windowCompactnessHypotheses P (j + 1)).time_bounds
  have hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0) :=
    Q.complete_interior 0 hGtime
  have hLcomplete : L.limitCarrier.metricComplete (L.limitFlow.metricAt 0) :=
    R.complete_interior 0 hLtime
  have hballs : ∀ k r,
      (S.smallBasedWindow j (G.subsequence k)).ballAt 0 r =
        (S.smallBasedWindow (j + 1) (L.subsequence k)).ballAt 0 r := by
    intro k r
    rfl
  have hmetrics : ∀ k t,
      t ∈ Ioo (compactnessLower j + 1) (compactnessUpper j + 1) →
      t ∈ Ioo (compactnessLower (j + 1) + 1) (compactnessUpper (j + 1) + 1) →
      (S.smallBasedWindow j (G.subsequence k)).metricAt t =
        (S.smallBasedWindow (j + 1) (L.subsequence k)).metricAt t := by
    intro k t _ _
    rfl
  obtain ⟨σ, hσ, e, hbase, hmetric, _, _⟩ :=
    PointedGeometricConvergence.exists_relative_pointed_flow_diffeomorph
      (smallRescalingCarrier (M := M)) (S.smallBasedWindow j) (S.smallBasedWindow (j + 1))
      G L hGtime hLtime hGcomplete hLcomplete hballs hmetrics
  refine ⟨{
    next := R.ofSubsequence.reselect σ hσ
    refinement := R.geometric_limit.subsequence ∘ σ
    refinement_strictMono := R.geometric_limit.subsequence_strictMono.comp hσ
    subsequence_eq := rfl
    equiv := e
    base_eq := hbase
    metric_inner_eq := hmetric }⟩

end PoincareConjecture.AncientRescalingSequence
