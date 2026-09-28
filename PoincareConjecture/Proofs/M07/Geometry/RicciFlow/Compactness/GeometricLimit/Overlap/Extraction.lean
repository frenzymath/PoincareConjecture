import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.SourceTransition

set_option autoImplicit false
open Set Filter Metric
open scoped Topology NNReal

namespace PoincareConjecture.ChartDistance

theorem exists_overlap_limits
    {X : ℕ → Type*} [∀ i, MetricSpace (X i)] [∀ i, Nonempty (X i)]
    [∀ i, LocallyCompactSpace (X i)] [∀ i, SigmaCompactSpace (X i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    (e : ∀ k i, X i → M k) (L : ℕ → ℝ≥0)
    (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hb : ∀ i j (x : X i) (y : X j), ∃ B : ℝ,
      ∀ k, dist (e k i x) (e k j y) ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ D : ∀ i j, C(X i × X j, ℝ),
      (∀ i j, TendstoLocallyUniformly
        (fun k (p : X i × X j) => dist (e (σ k) i p.1) (e (σ k) j p.2))
        (D i j) atTop) ∧
      ∃ τ : ∀ i j, OpenPartialHomeomorph (X i) (X j),
        (∀ i j (x : X i) (y : X j),
          x ∈ (τ i j).source ∧ τ i j x = y ↔ D i j (x, y) = 0) ∧
        (∀ i, (τ i i).source = univ) ∧
        (∀ i x, τ i i x = x) ∧
        (∀ i j l x, x ∈ (τ i j).source → τ i j x ∈ (τ j l).source →
          x ∈ (τ i l).source ∧ τ j l (τ i j x) = τ i l x) ∧
        (∀ i j, IsClosed {p : X i × X j |
          p.1 ∈ (τ i j).source ∧ τ i j p.1 = p.2}) ∧
        ∀ i j x, x ∈ (τ i j).source →
          Tendsto (fun k => Function.invFun (e (σ k) j) (e (σ k) i x))
            atTop (𝓝 (τ i j x)) := by
  obtain ⟨σ, hσ, D, hD⟩ := exists_pairwise_limits e L he hb
  have hpoint (i j : ℕ) (x : X i) (y : X j) :
      Tendsto (fun k => dist (e (σ k) i x) (e (σ k) j y)) atTop
        (𝓝 (D i j (x, y))) :=
    (hD i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let τ := overlapHomeomorph hpoint L (fun k => he (σ k)) c hc
    (fun k => hlower (σ k)) (fun k => hopen (σ k)) (fun k => hconn (σ k))
  refine ⟨σ, hσ, D, hD, τ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j x y
    exact (zero_iff_transition hpoint c hc (fun k => hlower (σ k))).symm
  · intro i
    exact overlap_self hpoint i
  · intro i x
    exact transition_self hpoint c hc (fun k => hlower (σ k)) i x
  · intro i j l x hx hy
    exact transition_cocycle hpoint c hc (fun k => hlower (σ k)) hx hy
  · intro i j
    have hset : {p : X i × X j | p.1 ∈ (τ i j).source ∧ τ i j p.1 = p.2} =
        {p | D i j p = 0} := by
      ext p
      exact (zero_iff_transition hpoint c hc (fun k => hlower (σ k))).symm
    rw [hset]
    exact isClosed_zero (D i j)
  · intro i j x hx
    exact tendsto_source_transition hpoint L (fun k => he (σ k)) c hc
      (fun k => hlower (σ k)) (fun k => hopen (σ k)) (fun k => hconn (σ k)) hx

end PoincareConjecture.ChartDistance
