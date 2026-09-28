import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.BoundaryEscape

set_option autoImplicit false
open Set Filter Metric
open scoped Topology NNReal

namespace PoincareConjecture.ChartDistance

theorem boundary_escape_of_reindexed_chart_approximation
    {ι : Type*} {X : ι → Type*} [∀ i, MetricSpace (X i)]
    [∀ i, WeaklyLocallyCompactSpace (X i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {e : ∀ k i, X i → M k} {D : ∀ i j, C(X i × X j, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : X i × X j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (O : Poincare.Gluing.OverlapSystem X)
    (hrel : ∀ i j (x : X i) (y : X j), O.Rel ⟨i, x⟩ ⟨j, y⟩ ↔ D i j (x, y) = 0)
    {σ : ℕ → ℕ} (hσ : StrictMono σ)
    {F : ∀ j, Quotient O.setoid → M (σ j)}
    (happrox : ∀ i K, IsCompact K → TendstoUniformlyOn
      (fun j x => dist (F j (O.include i x)) (e (σ j) i x)) (fun _ => 0) atTop K)
    {i₀ : ι} (p : X i₀) (E : ℕ → Set (Quotient O.setoid))
    (hcompact : ∀ l, IsCompact (frontier (E l)))
    (hradius : ∀ l q, q ∈ frontier (E l) →
      quotientRadius (fun i j x y => (hD i j).tendstoLocallyUniformlyOn.tendsto_at
        (mem_univ (x, y))) O hrel p q = (l : ℝ) + 1) :
    ∀ A : ℝ, 0 < A → ∃ l : ℕ, ∀ᶠ j in atTop, ∀ q ∈ frontier (E l),
      ENNReal.ofReal A ≤ edist (e (σ j) i₀ p) (F j q) := by
  have hDσ : ∀ i j, TendstoLocallyUniformly
      (fun k (p : X i × X j) => dist (e (σ k) i p.1) (e (σ k) j p.2))
      (D i j) atTop := by
    intro i j u hu x
    obtain ⟨V, hV, heventual⟩ := hD i j u hu x
    exact ⟨V, hV, hσ.tendsto_atTop.eventually heventual⟩
  exact boundary_escape_of_chart_approximation hDσ O hrel happrox p E hcompact hradius

end PoincareConjecture.ChartDistance
