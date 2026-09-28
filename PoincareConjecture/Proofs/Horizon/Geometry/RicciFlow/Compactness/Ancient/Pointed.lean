import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

noncomputable def spatialPullbackInner {n : ℕ} (L C : FlowCarrier n)
    (g : C.metric) (f : L.carrier → C.carrier) (x : L.carrier)
    (v w : L.tangent x) : ℝ :=
  letI := L.topologicalSpace
  letI := L.chartedSpace
  letI := L.isManifold
  letI := C.topologicalSpace
  letI := C.chartedSpace
  letI := C.isManifold
  g.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w)

structure AncientPointedGeometricConvergence {n : ℕ}
    (C : ℕ → FlowCarrier.{0} n) (g : ∀ k, ℝ → (C k).metric)
    (p : ∀ k, (C k).carrier) (T : ℝ) where
  limitCarrier : FlowCarrier.{0} n
  limitFlow : @RicciFlow n limitCarrier.carrier limitCarrier.topologicalSpace
    limitCarrier.chartedSpace limitCarrier.isManifold (Iio T)
  base : limitCarrier.carrier
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  exhaustion : ℕ → Set limitCarrier.carrier
  exhaustion_open : ∀ j, letI := limitCarrier.topologicalSpace
    IsOpen (exhaustion j)
  exhaustion_connected : ∀ j, letI := limitCarrier.topologicalSpace
    IsConnected (exhaustion j)
  exhaustion_compactClosure : ∀ j, letI := limitCarrier.topologicalSpace
    IsCompact (closure (exhaustion j))
  exhaustion_increasing : ∀ j, exhaustion j ⊆ exhaustion (j + 1)
  exhaustion_covers : ⋃ j, exhaustion j = univ
  embedding : ∀ k, limitCarrier.carrier → (C (subsequence k)).carrier
  embedding_open : ∀ k, letI := limitCarrier.topologicalSpace
    letI := (C (subsequence k)).topologicalSpace
    Topology.IsOpenEmbedding (fun x : exhaustion k => embedding k x)
  embedding_smooth : ∀ k, letI := limitCarrier.topologicalSpace
    letI := limitCarrier.chartedSpace
    letI := (C (subsequence k)).topologicalSpace
    letI := (C (subsequence k)).chartedSpace
    IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (embedding k) (exhaustion k)
  base_in_exhaustion : ∀ j, base ∈ exhaustion j
  base_preserving : ∀ k, embedding k base = p (subsequence k)
  pullback_metric_converges : letI := limitCarrier.topologicalSpace
    letI := limitCarrier.chartedSpace
    letI := limitCarrier.isManifold
    ∀ j K I, IsCompact K → K ⊆ exhaustion j → IsCompact I → I ⊆ Iio T →
      ∀ ε > 0, ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N, ∀ t ∈ I, ∀ x ∈ K,
        ∀ v w : limitCarrier.tangent x,
          limitCarrier.metricNorm (limitFlow.metric t) x v ≤ 1 →
          limitCarrier.metricNorm (limitFlow.metric t) x w ≤ 1 →
          |spatialPullbackInner limitCarrier (C (subsequence k))
              (g (subsequence k) t) (embedding k) x v w -
            limitCarrier.metricInner (limitFlow.metric t) x v w| < ε
  pullback_metric_CInfinity : letI := limitCarrier.topologicalSpace
    letI := limitCarrier.chartedSpace
    letI := limitCarrier.isManifold
    ∀ q : limitCarrier.carrier, ∀ j r : ℕ,
      ∀ K : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsCompact K →
      K ⊆ {z | z.1 ∈ Iio T ∧ z.2 ∈ (extChartAt (𝓡 n) q).target ∧
        (extChartAt (𝓡 n) q).symm z.2 ∈ exhaustion j} →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N,
        ∀ a b : Fin n, ∀ z ∈ K,
          ‖MetricJet r
              (FlowCarrier.coordinateCoefficient limitCarrier q
                (fun t x v w => spatialPullbackInner limitCarrier (C (subsequence k))
                  (g (subsequence k) t) (embedding k) x v w) a b) K z -
            MetricJet r
              (FlowCarrier.coordinateCoefficient limitCarrier q
                (fun t x v w => limitCarrier.metricInner
                  (limitFlow.metric t) x v w) a b) K z‖ < ε

end PoincareConjecture
