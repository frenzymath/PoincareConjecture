import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.Exhaustion
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.Boundary











set_option autoImplicit false
open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

theorem exists_pointed_source_exhaustion_with_boundary_escape
    {n : ℕ} (U : ℕ → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {e : ∀ k i, Piece U i → M k}
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : Piece U i × Piece U j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (L : ℕ → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    {i₀ : ℕ} (p : Piece U i₀)
    (hcover : ∀ R : ℝ, 0 < R → ∃ s : Finset ℕ, ∃ K : ∀ i, Set (Piece U i),
      (∀ i ∈ s, IsCompact (K i)) ∧
        ∀ᶠ k in atTop, ball (e k i₀ p) R ⊆ ⋃ i ∈ s, e k i '' K i) :
    letI : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
    let O := overlapSystem (fun l q x y =>
      (hD l q).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))) L he c hc hlower hopen hconn
    letI := quotientChartedSpace U hU O
    ConnectedSpace (Quotient O.setoid) ∧
    ∃ E : ℕ → Set (Quotient O.setoid),
      (∀ j, IsOpen (E j)) ∧ (∀ j, IsConnected (E j)) ∧
      (∀ j, O.include i₀ p ∈ E j) ∧ (∀ j, IsCompact (closure (E j))) ∧
      (∀ j, closure (E j) ⊆ E (j + 1)) ∧ (⋃ j, E j) = univ ∧
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ F : ∀ j, Quotient O.setoid → M (σ j),
      (∀ j, Topology.IsOpenEmbedding (fun x : E j => F j x) ∧
        IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (F j) (E j) ∧
        F j (O.include i₀ p) = e (σ j) i₀ p) ∧
      (∀ i C, IsCompact C → TendstoUniformlyOn
        (fun j x => dist (F j (O.include i x)) (e (σ j) i x)) (fun _ => 0) atTop C) ∧
      (∀ i m B, IsCompact B → B ⊆ U i →
        TendstoUniformlyOn (fun j => iteratedFDeriv ℝ m
          (coordinateRepresentative U hU
            (fun x => Function.invFun (e (σ j) i) (F j (O.include i x)))))
          (iteratedFDeriv ℝ m id) atTop B) ∧
      ∀ A : ℝ, 0 < A → ∃ l : ℕ, ∀ᶠ j in atTop, ∀ q ∈ frontier (E l),
        ENNReal.ofReal A ≤ edist (e (σ j) i₀ p) (F j q) := by
  let : ∀ l, LocallyCompactSpace (Piece U l) := fun l => (hU l).locallyCompactSpace
  let : ∀ l, LocallyConnectedSpace (Piece U l) := fun l => (hU l).locallyConnectedSpace
  let hp := fun l q x y => (hD l q).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let O := overlapSystem hp L he c hc hlower hopen hconn
  let := quotientChartedSpace U hU O
  have hrel : ∀ i j (x : Piece U i) (y : Piece U j), O.Rel ⟨i, x⟩ ⟨j, y⟩ ↔ D i j (x, y) = 0 :=
    fun i j x y => (zero_iff_transition hp c hc hlower).symm
  obtain ⟨hQ, E, hE, hEc, hEp, hEK, hEstep, hEcover, hEradius⟩ :=
    exists_connected_exhaustion_of_source_ball_covers hp O hrel hD L he hconn p hcover
  obtain ⟨σ, hσ, V, hV, F, hF, happrox, hjet⟩ :=
    exists_pointed_source_embeddings_on_compact_sequence U hU hD L he c hc hlower
      hopen hconn hsmooth hbound p (fun j => closure (E j)) hEK
  refine ⟨hQ, E, hE, hEc, hEp, hEK, hEstep, hEcover, σ, hσ, F, ?_, happrox, hjet, ?_⟩
  · intro j
    have hEV : E j ⊆ V j := subset_closure.trans
      (subset_union_left.trans (hV j).2.2)
    exact ⟨(hF j).1.comp (.inclusion hEV ((hE j).preimage continuous_subtype_val)),
      (fun x => (hF j).2.1 ⟨x, hEV x.property⟩), (hF j).2.2⟩
  · exact boundary_escape_of_reindexed_chart_approximation hD O hrel hσ happrox p E
      (fun j => (hEK j).of_isClosed_subset isClosed_frontier frontier_subset_closure) hEradius

end PoincareConjecture.ChartDistance
