import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.FlowCarrier
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28



structure PartialPointedMetricConvergence {n : ℕ} {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (g : ∀ k, RiemannianMetric n (M k)) (p : ∀ k, M k) (A : ℝ) where

  limitCarrier : FlowCarrier.{0} n

  limitMetric : limitCarrier.metric

  base : limitCarrier.carrier

  subsequence : ℕ → ℕ

  subsequence_strictMono : StrictMono subsequence

  exhaustion : ℕ → Set limitCarrier.carrier

  exhaustion_open : letI := limitCarrier.topologicalSpace
    ∀ j, IsOpen (exhaustion j)

  exhaustion_connected : letI := limitCarrier.topologicalSpace
    ∀ j, IsConnected (exhaustion j)

  base_in_exhaustion : ∀ j, base ∈ exhaustion j

  exhaustion_compactClosure : letI := limitCarrier.topologicalSpace
    ∀ j, IsCompact (closure (exhaustion j))

  exhaustion_step : letI := limitCarrier.topologicalSpace
    ∀ j, closure (exhaustion j) ⊆ exhaustion (j + 1)

  exhaustion_covers : (⋃ j, exhaustion j) = univ

  embedding : ∀ j, limitCarrier.carrier → M (subsequence j)

  embedding_open : letI := limitCarrier.topologicalSpace
    ∀ j, Topology.IsOpenEmbedding (fun x : exhaustion j => embedding j x)

  embedding_smooth : letI := limitCarrier.topologicalSpace
    letI := limitCarrier.chartedSpace
    ∀ j, IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (embedding j) (exhaustion j)

  base_preserving : ∀ j, embedding j base = p (subsequence j)


  metric_jets : letI := limitCarrier.topologicalSpace
    letI := limitCarrier.chartedSpace
    letI := limitCarrier.isManifold
    ∀ q m K, IsCompact K → K ⊆ (extChartAt (𝓡 n) q).target →
      TendstoUniformlyOn
        (fun j => iteratedFDeriv ℝ m ((g (subsequence j)).pullbackCoefficients
          (embedding j ∘ (extChartAt (𝓡 n) q).symm)))
        (iteratedFDeriv ℝ m (limitMetric.pullbackCoefficients
          (extChartAt (𝓡 n) q).symm)) atTop K


  boundary_control : letI := limitCarrier.topologicalSpace
    ∀ B : ℝ, B < A → ∃ l : ℕ, ∀ᶠ j in atTop, ∀ q ∈ frontier (exhaustion l),
      ENNReal.ofReal B ≤ (g (subsequence j)).edist (p (subsequence j)) (embedding j q)



noncomputable def PartialPointedMetricConvergence.reindex
    {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k} {A : ℝ}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (G : PartialPointedMetricConvergence (fun k => g (φ k)) (fun k => p (φ k)) A) :
    PartialPointedMetricConvergence g p A where
  limitCarrier := G.limitCarrier
  limitMetric := G.limitMetric
  base := G.base
  subsequence := φ ∘ G.subsequence
  subsequence_strictMono := hφ.comp G.subsequence_strictMono
  exhaustion := G.exhaustion
  exhaustion_open := G.exhaustion_open
  exhaustion_connected := G.exhaustion_connected
  base_in_exhaustion := G.base_in_exhaustion
  exhaustion_compactClosure := G.exhaustion_compactClosure
  exhaustion_step := G.exhaustion_step
  exhaustion_covers := G.exhaustion_covers
  embedding := G.embedding
  embedding_open := G.embedding_open
  embedding_smooth := G.embedding_smooth
  base_preserving := G.base_preserving
  metric_jets := G.metric_jets
  boundary_control := G.boundary_control

end PoincareConjecture.M28
