import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.CompleteStaticLimit
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.JetBounds
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Diagonal










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

universe u

namespace PoincareConjecture.M30

open ChartDistance




theorem exists_complete_static_limit_of_controlled_charts
    {n : ℕ} (U : ℕ → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (e : ∀ k i, Piece U i → M k)
    (L : ℕ → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))
    (hb : ∀ i j (x : Piece U i) (y : Piece U j),
      ∃ C : ℝ, ∀ k, dist (e k i x) (e k j y) ≤ C)
    {i₀ : ℕ} (p : Piece U i₀)
    (hcover : ∀ R : ℝ, 0 < R → ∃ s : Finset ℕ,
      ∃ K : ∀ i, Set (Piece U i), (∀ i ∈ s, IsCompact (K i)) ∧
        ∀ᶠ k in atTop, ball (e k i₀ p) R ⊆ ⋃ i ∈ s, e k i '' K i)
    (g : ∀ k, RiemannianMetric n (M k))
    (hdist : ∀ k (x y : M k), edist x y = (g k).edist x y)
    (hjets : ∀ i, LocallyEventuallyBoundedDerivatives (U i)
      (fun k => (g k).pullbackCoefficients (chartParametrization U hU (e k i))))
    (helliptic : ∀ i K, IsCompact K → K ⊆ U i →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v,
        a * ‖v‖ ^ 2 ≤
          (g k).pullbackCoefficients (chartParametrization U hU (e k i)) x v v) :
    ∃ G : PartialPointedMetricConvergence g (fun k => e k i₀ p) 1,
      G.limitCarrier.metricComplete G.limitMetric ∧
        ∀ R : ℝ, 0 < R → ∃ l : ℕ, ∀ᶠ k in atTop,
          (g (G.subsequence k)).ball (e (G.subsequence k) i₀ p) R ⊆
            G.embedding k '' G.exhaustion l := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  have hsource (i k : ℕ) : ContDiffOn ℝ ∞
      ((g k).pullbackCoefficients (chartParametrization U hU (e k i))) (U i) := by
    intro x hx
    exact ((g k).contDiffAt_pullbackCoefficients
      ((contMDiffOn_chartParametrization U hU (hsmooth k i).contMDiff).contMDiffAt
        ((hU i).mem_nhds hx))).contDiffWithinAt
  obtain ⟨sigma, hsigma, B, hBsmooth, hBjets⟩ := exists_common_smoothSubsequenceExtraction hU
    (fun i k => (g k).pullbackCoefficients (chartParametrization U hU (e k i)))
    hsource hjets
  obtain ⟨tau, htau, D, hD⟩ := exists_pairwise_limits (fun k => e (sigma k)) L
    (fun k => he (sigma k)) (fun i j x y => by
      obtain ⟨C, hC⟩ := hb i j x y
      exact ⟨C, fun k => hC (sigma k)⟩)
  let rho := sigma ∘ tau
  have hrho : StrictMono rho := hsigma.comp htau
  have hjets' : ∀ i, LocallyEventuallyBoundedDerivatives (U i)
      (fun k => (g (rho k)).pullbackCoefficients
        (chartParametrization U hU (e (rho k) i))) := by
    intro i K hK hKU m
    obtain ⟨C, hC⟩ := hjets i K hK hKU m
    exact ⟨C, hrho.tendsto_atTop.eventually hC⟩
  have helliptic' : ∀ i K, IsCompact K → K ⊆ U i →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v,
        a * ‖v‖ ^ 2 ≤ (g (rho k)).pullbackCoefficients
          (chartParametrization U hU (e (rho k) i)) x v v := by
    intro i K hK hKU
    obtain ⟨a, ha, hbound⟩ := helliptic i K hK hKU
    exact ⟨a, ha, hrho.tendsto_atTop.eventually hbound⟩
  have hbound := locallyEventuallyBoundedDerivatives_source_transition U hU
    (fun i j x y => (hD i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y)))
    L (fun k => he (rho k)) c hc (fun k => hlower (rho k)) (fun k => hopen (rho k))
    (fun k => hconn (rho k)) (fun k => hsmooth (rho k)) (fun k => g (rho k))
    hjets' helliptic'
  have hcover' : ∀ R : ℝ, 0 < R → ∃ s : Finset ℕ,
      ∃ K : ∀ i, Set (Piece U i), (∀ i ∈ s, IsCompact (K i)) ∧
        ∀ᶠ k in atTop, ball (e (rho k) i₀ p) R ⊆ ⋃ i ∈ s, e (rho k) i '' K i := by
    intro R hR
    obtain ⟨s, K, hK, htail⟩ := hcover R hR
    exact ⟨s, K, hK, hrho.tendsto_atTop.eventually htail⟩
  obtain ⟨G, hcomplete, hcoverage⟩ := exists_complete_static_limit_of_coordinate_limits
    U hU hD L (fun k => he (rho k)) c hc (fun k => hlower (rho k))
    (fun k => hopen (rho k)) (fun k => hconn (rho k)) (fun k => hsmooth (rho k))
    hbound p hcover' (fun k => g (rho k)) (fun k => hdist (rho k)) B hBsmooth
    (fun i m K hK hKU V hV => htau.tendsto_atTop.eventually (hBjets i m K hK hKU V hV))
    (by
      intro i x hx
      obtain ⟨a, ha, hbound⟩ := helliptic' i {x} isCompact_singleton
        (singleton_subset_iff.mpr hx)
      exact ⟨a, ha, hbound.mono fun _ hk => hk x (mem_singleton x)⟩)
  exact ⟨G.reindex hrho, hcomplete, hcoverage⟩

end PoincareConjecture.M30
