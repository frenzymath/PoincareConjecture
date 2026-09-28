import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Distance

set_option autoImplicit false
open Set Filter Metric
open scoped Topology

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {M : ℕ → Type*} [∀ k, PseudoMetricSpace (M k)]
    {e : ∀ k i, X i → M k} {D : ∀ i j, X i × X j → ℝ}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : X i × X j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)

include hD

theorem eventually_dist_sub_limit_lt_on_compact
    {i j : ι} (K : Set (X i × X j)) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ p ∈ K,
      |dist (e k i p.1) (e k j p.2) - D i j p| < ε := by
  have hconv := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((hD i j).tendstoLocallyUniformlyOn.mono (subset_univ K))
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv ε hε] with k hk p hp
  simpa only [Real.dist_eq, abs_sub_comm] using hk p hp

theorem eventually_base_dist_sub_limit_lt_on_finite_compacts
    {i₀ : ι} (p : X i₀) (s : Finset ι) (K : ∀ i, Set (X i))
    (hK : ∀ i ∈ s, IsCompact (K i)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ i ∈ s, ∀ x ∈ K i,
      |dist (e k i₀ p) (e k i x) - D i₀ i (p, x)| < ε := by
  have h := fun i hi => eventually_dist_sub_limit_lt_on_compact hD
    ({p} ×ˢ K i) (isCompact_singleton.prod (hK i hi)) hε
  filter_upwards [s.eventually_all.mpr h] with k hk i hi x hx
  exact hk i hi (p, x) ⟨mem_singleton p, hx⟩

theorem eventually_source_dist_gt_of_limit_lower_bound
    {i₀ : ι} (p : X i₀) (s : Finset ι) (K : ∀ i, Set (X i))
    (hK : ∀ i ∈ s, IsCompact (K i)) {r R : ℝ} (hr : r < R)
    (hlower : ∀ i ∈ s, ∀ x ∈ K i, R ≤ D i₀ i (p, x)) :
    ∀ᶠ k in atTop, ∀ i ∈ s, ∀ x ∈ K i, r < dist (e k i₀ p) (e k i x) := by
  filter_upwards [eventually_base_dist_sub_limit_lt_on_finite_compacts hD p s K hK
    (sub_pos.mpr hr)] with k hk i hi x hx
  have h := (abs_lt.mp (hk i hi x hx)).1
  have hR := hlower i hi x hx
  linarith

end PoincareConjecture.ChartDistance
