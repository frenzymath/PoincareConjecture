import PoincareConjecture.Proofs.M28.Mathlib.SublevelExhaustion
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Connectedness
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.BoundaryEscape
import Mathlib.Topology.Order.IsLUB

set_option autoImplicit false

open Set Filter Metric
open scoped Topology NNReal

namespace PoincareConjecture.ChartDistance

theorem exists_partial_radius_exhaustion
    {ι : Type*} {X : ι → Type*} [∀ i, MetricSpace (X i)]
    [∀ i, LocallyConnectedSpace (X i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {e : ∀ k i, X i → M k} {D : ∀ i j, C(X i × X j, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : X i × X j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (O : Poincare.Gluing.OverlapSystem X)
    (hrel : ∀ i j (x : X i) (y : X j), O.Rel ⟨i, x⟩ ⟨j, y⟩ ↔ D i j (x, y) = 0)
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    {i₀ : ι} (p : X i₀) (A : ℝ) (hA : 0 < A)
    (hrange : ∀ i (x : X i), D i₀ i (p, x) < A)
    (hcover : ∀ R : ℝ, 0 < R → R < A → ∃ s : Finset ι,
      ∃ K : ∀ j, Set (X j), (∀ j ∈ s, IsCompact (K j)) ∧
        ∀ᶠ k in atTop, ball (e k i₀ p) R ⊆ ⋃ j ∈ s, e k j '' K j) :
    ConnectedSpace (Quotient O.setoid) ∧
    ∃ r : ℕ → ℝ, StrictMono r ∧ (∀ n, r n ∈ Ioo 0 A) ∧ Tendsto r atTop (𝓝 A) ∧
    ∃ V : ℕ → Set (Quotient O.setoid),
      (∀ n, IsOpen (V n)) ∧ (∀ n, IsConnected (V n)) ∧
      (∀ n, O.include i₀ p ∈ V n) ∧ (∀ n, IsCompact (closure (V n))) ∧
      (∀ n, closure (V n) ⊆ V (n + 1)) ∧ (⋃ n, V n) = univ ∧
      ∀ n q, q ∈ frontier (V n) →
        quotientRadius (fun i j x y => (hD i j).tendstoLocallyUniformlyOn.tendsto_at
          (mem_univ (x, y))) O hrel p q = r n := by
  have hp := fun i j x y =>
    (hD i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let : PreconnectedSpace (Quotient O.setoid) :=
    quotient_preconnected_of_local_source_ball_covers hD O hrel L he hconn p (by
      intro i x
      obtain ⟨R, hxR, hRA⟩ := exists_between (hrange i x)
      have hR := (nonneg hp i₀ i p x).trans_lt hxR
      exact ⟨R, hR, hxR, hcover R hR hRA⟩)
  let : LocallyConnectedSpace (Quotient O.setoid) := quotient_locallyConnected_of_charts O
  let : Nonempty (Quotient O.setoid) := ⟨O.include i₀ p⟩
  obtain ⟨r, hr, hrA, hrlim⟩ := exists_seq_strictMono_tendsto' hA
  refine ⟨⟨⟨O.include i₀ p⟩⟩, r, hr, hrA, hrlim, ?_⟩
  apply (quotientRadius hp O hrel p).continuous.exists_connected_sublevel_exhaustion
    (O.include i₀ p) r hr
  · intro n
    simpa only [quotientRadius_base] using (hrA n).1
  · intro n
    obtain ⟨R, hrR, hRA⟩ := exists_between (hrA n).2
    obtain ⟨s, K, hK, hcov⟩ := hcover R ((hrA n).1.trans hrR) hRA
    exact isCompact_radius_sublevel_of_source_ball_cover hp O hrel L he s K hK p hrR hcov
  · intro q
    induction q using Quotient.inductionOn with
    | h q => exact (hrlim.eventually (lt_mem_nhds (hrange q.1 q.2))).exists

theorem partial_boundary_control_of_chart_approximation
    {ι : Type*} {X : ι → Type*} [∀ i, MetricSpace (X i)]
    [∀ i, WeaklyLocallyCompactSpace (X i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {e : ∀ k i, X i → M k} {D : ∀ i j, C(X i × X j, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : X i × X j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (O : Poincare.Gluing.OverlapSystem X)
    (hrel : ∀ i j (x : X i) (y : X j), O.Rel ⟨i, x⟩ ⟨j, y⟩ ↔ D i j (x, y) = 0)
    {F : ∀ k, Quotient O.setoid → M k}
    (happrox : ∀ i K, IsCompact K → TendstoUniformlyOn
      (fun k x => dist (F k (O.include i x)) (e k i x)) (fun _ => 0) atTop K)
    {i₀ : ι} (p : X i₀) (V : ℕ → Set (Quotient O.setoid))
    (hcompact : ∀ n, IsCompact (frontier (V n)))
    {A : ℝ} {r : ℕ → ℝ} (hrlim : Tendsto r atTop (𝓝 A))
    (hradius : ∀ n q, q ∈ frontier (V n) →
      quotientRadius (fun i j x y => (hD i j).tendstoLocallyUniformlyOn.tendsto_at
        (mem_univ (x, y))) O hrel p q = r n) :
    ∀ B : ℝ, B < A → ∃ n : ℕ, ∀ᶠ k in atTop, ∀ q ∈ frontier (V n),
      ENNReal.ofReal B ≤ edist (e k i₀ p) (F k q) := by
  intro B hBA
  obtain ⟨n, hn⟩ := (hrlim.eventually (lt_mem_nhds hBA)).exists
  have hconv := tendstoUniformlyOn_quotientRadius_of_chart_approximation
    hD O hrel happrox p (hcompact n) isClosed_frontier
  refine ⟨n, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv (r n - B) (sub_pos.mpr hn)]
    with k hk q hq
  have hd := hk q hq
  rw [hradius n q hq, Real.dist_eq] at hd
  have hlower : B ≤ dist (e k i₀ p) (F k q) := by
    have := (abs_lt.mp hd).2
    linarith
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal hlower

end PoincareConjecture.ChartDistance
