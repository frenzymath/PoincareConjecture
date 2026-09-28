import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Producer
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Exhaustion
import PoincareConjecture.Proofs.M07.Topology.Sequences.Diagonal


















set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture



structure PointedGeometricConvergenceCore
    {n : ℕ} {T' T : ℝ} (S : PointedFlowSequence n T' T)
    (L : FlowCarrier n) (F : BasedFlow n T' T L) (φ : ℕ → ℕ) where
  exhaustion : ℕ → Set L.carrier
  exhaustion_open : ∀ j,
    letI : TopologicalSpace L.carrier := L.topologicalSpace
    IsOpen (exhaustion j)
  exhaustion_connected : ∀ j,
    letI : TopologicalSpace L.carrier := L.topologicalSpace
    IsConnected (exhaustion j)
  exhaustion_compactClosure : ∀ j,
    letI : TopologicalSpace L.carrier := L.topologicalSpace
    IsCompact (closure (exhaustion j))
  exhaustion_increasing : ∀ j, exhaustion j ⊆ exhaustion (j + 1)
  exhaustion_covers : ⋃ j, exhaustion j = Set.univ
  embedding : ∀ j,
    SmoothSpacetimeEmbedding F (S.flow (φ j))
      (Set.Ioo T' T ×ˢ exhaustion j)
  base_in_exhaustion : ∀ j, F.base ∈ exhaustion j
  base_preserving : ∀ j,
    (embedding j).toFun (0, F.base) = (0, (S.flow (φ j)).base)
  pullback_metric_converges :
    letI : TopologicalSpace L.carrier := L.topologicalSpace
    ∀ j K I, IsCompact K → K ⊆ exhaustion j → IsCompact I →
      I ⊆ Set.Ioo T' T → ∀ ε > 0, ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N,
        ∀ t ∈ I, ∀ x ∈ K, ∀ v w : L.tangent x,
          L.metricNorm (F.metricAt t) x v ≤ 1 →
          L.metricNorm (F.metricAt t) x w ≤ 1 →
          |pullbackInnerValue F (S.flow (φ k)) (embedding k) t x v w -
            L.metricInner (F.metricAt t) x v w| < ε
  pullback_metric_CInfinity :
    letI : TopologicalSpace L.carrier := L.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) L.carrier := L.chartedSpace
    letI : IsManifold (𝓡 n) ∞ L.carrier := L.isManifold
    ∀ q : L.carrier, ∀ j r : ℕ,
      ∀ K : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsCompact K →
      K ⊆ {p | p.1 ∈ Set.Ioo T' T ∧
        p.2 ∈ (extChartAt (𝓡 n) q).target ∧
        (extChartAt (𝓡 n) q).symm p.2 ∈ exhaustion j} →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N,
        ∀ a b : Fin n, ∀ p ∈ K,
          ‖MetricJet r
              (FlowCarrier.coordinateCoefficient L q
                (pullbackInnerValue F (S.flow (φ k)) (embedding k))
                a b) K p -
            MetricJet r
              (FlowCarrier.coordinateCoefficient L q
                (fun t x v w ↦ L.metricInner (F.metricAt t) x v w)
                a b) K p‖ < ε



def PointedGeometricConvergenceCore.toGeometricLimit
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    {L : FlowCarrier n} {F : BasedFlow n T' T L} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (C : PointedGeometricConvergenceCore S L F φ) :
    PointedGeometricConvergence S := by
  letI : TopologicalSpace L.carrier := L.topologicalSpace
  exact
    { limitCarrier := L
      limitFlow := F
      subsequence := φ
      subsequence_strictMono := hφ
      exhaustion := C.exhaustion
      exhaustion_open := C.exhaustion_open
      exhaustion_connected := C.exhaustion_connected
      exhaustion_compactClosure := C.exhaustion_compactClosure
      exhaustion_increasing := C.exhaustion_increasing
      exhaustion_covers := C.exhaustion_covers
      embedding := C.embedding
      base_in_exhaustion := C.base_in_exhaustion
      base_preserving := C.base_preserving
      pullback_metric_converges := C.pullback_metric_converges
      pullback_metric_CInfinity := C.pullback_metric_CInfinity }


def PointedGeometricConvergenceCore.toProducer
    {n : ℕ} {T' T : ℝ} {H : PointedRicciFlowCompactnessHypotheses n T' T}
    {L : FlowCarrier n} {F : BasedFlow n T' T L} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (C : PointedGeometricConvergenceCore H.sequence L F φ) :
    PointedRicciFlowGeometricProducer H where
  geometric_limit := C.toGeometricLimit hφ

end PoincareConjecture

namespace Poincare


theorem exists_diagonal_stage_selection
    {P : ℕ → ℕ → Prop} (hP : ∀ j, ∀ᶠ k in Filter.atTop, P j k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k j, j ≤ k → P j (φ k) := by
  exact exists_strictMono_forall_le_of_eventually hP

end Poincare
