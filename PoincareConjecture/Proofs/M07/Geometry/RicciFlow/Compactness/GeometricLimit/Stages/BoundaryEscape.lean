import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.CompactRepresentatives
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Radius












set_option autoImplicit false
open Set Filter Metric
open scoped Topology NNReal

namespace PoincareConjecture.ChartDistance

theorem tendstoUniformlyOn_source_displacement_of_corrections
    {Y : Type*} [MetricSpace Y] {N : ℕ → Type*} [∀ k, MetricSpace (N k)]
    {f : ∀ k, Y → N k} {L : ℝ≥0} (hf : ∀ k, LipschitzWith L (f k))
    {a : ℕ → Y → Y} {K : Set Y} (ha : TendstoUniformlyOn a id atTop K) :
    TendstoUniformlyOn (fun k x => dist (f k (a k x)) (f k x)) (fun _ => 0) atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp ha (ε / ((L : ℝ) + 1))
    (by positivity)] with k hk x hx
  have hsmall : ((L : ℝ) + 1) * dist (a k x) x < ε := by
    have h := hk x hx
    rw [id_eq, dist_comm] at h
    simpa only [mul_comm] using (lt_div_iff₀ (by positivity : 0 < (L : ℝ) + 1)).mp h
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg dist_nonneg]
  exact ((hf k).dist_le_mul _ _).trans_lt
    ((mul_le_mul_of_nonneg_right (by linarith : (L : ℝ) ≤ L + 1)
      dist_nonneg).trans_lt hsmall)

variable {ι : Type*} {X : ι → Type*} [∀ i, MetricSpace (X i)]
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

include hD hrel in
omit [∀ i, WeaklyLocallyCompactSpace (X i)] in
theorem tendstoUniformlyOn_chart_approximation_of_finite_cover
    {α : Type*} (s : Finset α) (a : α → ι)
    (C : ∀ b, Set (X (a b))) (hC : ∀ b ∈ s, IsCompact (C b))
    (hF : ∀ b ∈ s, TendstoUniformlyOn
      (fun k x => dist (F k (O.include (a b) x)) (e k (a b) x)) (fun _ => 0) atTop (C b))
    {i₀ : ι} {K : Set (X i₀)} (hK : IsCompact K)
    (hcover : O.include i₀ '' K ⊆ ⋃ b ∈ s, O.include (a b) '' C b) :
    TendstoUniformlyOn (fun k x => dist (F k (O.include i₀ x)) (e k i₀ x))
      (fun _ => 0) atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have herror := s.eventually_all.mpr (fun i hi =>
    Metric.tendstoUniformlyOn_iff.mp (hF i hi) (ε / 2) (by positivity))
  have hdist := s.eventually_all.mpr (fun i hi =>
    eventually_dist_sub_limit_lt_on_compact hD (C i ×ˢ K) ((hC i hi).prod hK)
      (show 0 < ε / 2 by positivity))
  filter_upwards [herror, hdist] with k hkF hkD x hx
  obtain ⟨i, hi, y, hy, heq⟩ := by
    simpa only [mem_iUnion, exists_prop, mem_image] using hcover (mem_image_of_mem _ hx)
  have hzero : D (a i) i₀ (y, x) = 0 :=
    (hrel (a i) i₀ y x).mp (Quotient.exact heq)
  have hd : dist (e k (a i) y) (e k i₀ x) < ε / 2 := by
    simpa only [hzero, sub_zero, abs_of_nonneg dist_nonneg]
      using hkD i hi (y, x) ⟨hy, hx⟩
  have hf : dist (F k (O.include (a i) y)) (e k (a i) y) < ε / 2 := by
    simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg dist_nonneg]
      using hkF i hi y hy
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg dist_nonneg]
  calc
    _ = dist (F k (O.include (a i) y)) (e k i₀ x) := by rw [heq]
    _ ≤ dist (F k (O.include (a i) y)) (e k (a i) y) + dist (e k (a i) y) (e k i₀ x) :=
      dist_triangle _ _ _
    _ < ε := by linarith

include hD happrox in
theorem tendstoUniformlyOn_quotientRadius_of_chart_approximation
    {i₀ : ι} (p : X i₀) {Q : Set (Quotient O.setoid)}
    (hQ : IsCompact Q) (hQc : IsClosed Q) :
    TendstoUniformlyOn (fun k q => dist (e k i₀ p) (F k q))
      (quotientRadius (fun i j x y => (hD i j).tendstoLocallyUniformlyOn.tendsto_at
        (mem_univ (x, y))) O hrel p) atTop Q := by
  obtain ⟨s, K, hK, hcover⟩ := exists_finite_compact_representatives O hQ hQc
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have herror := s.eventually_all.mpr (fun a ha =>
    Metric.tendstoUniformlyOn_iff.mp (happrox a.1 (K a) (hK a ha))
      (ε / 2) (by positivity))
  filter_upwards [eventually_base_dist_sub_limit_lt_on_representatives hD p s K hK
      (show 0 < ε / 2 by positivity), herror] with k hkD hkF q hq
  obtain ⟨a, ha, x, hx, rfl⟩ := by
    simpa only [← hcover, mem_iUnion, exists_prop, mem_image] using hq
  have hd : dist (D i₀ a.1 (p, x)) (dist (e k i₀ p) (e k a.1 x)) < ε / 2 := by
    simpa only [Real.dist_eq, abs_sub_comm] using hkD a ha x hx
  have hf : dist (F k (O.include a.1 x)) (e k a.1 x) < ε / 2 := by
    simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg dist_nonneg]
      using hkF a ha x hx
  change dist (D i₀ a.1 (p, x)) (dist (e k i₀ p) (F k (O.include a.1 x))) < ε
  calc
    _ ≤ dist (D i₀ a.1 (p, x)) (dist (e k i₀ p) (e k a.1 x)) +
        dist (dist (e k i₀ p) (e k a.1 x))
          (dist (e k i₀ p) (F k (O.include a.1 x))) := dist_triangle _ _ _
    _ ≤ dist (D i₀ a.1 (p, x)) (dist (e k i₀ p) (e k a.1 x)) +
        dist (F k (O.include a.1 x)) (e k a.1 x) := by
      gcongr
      simpa only [dist_self, zero_add, dist_comm] using
        dist_dist_dist_le (e k i₀ p) (e k a.1 x) (e k i₀ p) (F k (O.include a.1 x))
    _ < ε := by linarith

include hD happrox in
theorem boundary_escape_of_chart_approximation
    {i₀ : ι} (p : X i₀) (V : ℕ → Set (Quotient O.setoid))
    (hcompact : ∀ j, IsCompact (frontier (V j)))
    (hradius : ∀ j q, q ∈ frontier (V j) →
      quotientRadius (fun i j x y => (hD i j).tendstoLocallyUniformlyOn.tendsto_at
        (mem_univ (x, y))) O hrel p q = (j : ℝ) + 1) :
    ∀ A : ℝ, 0 < A → ∃ j : ℕ, ∀ᶠ k in atTop, ∀ q ∈ frontier (V j),
      ENNReal.ofReal A ≤ edist (e k i₀ p) (F k q) := by
  intro A _
  obtain ⟨j, hj⟩ := exists_nat_gt A
  have hconv := tendstoUniformlyOn_quotientRadius_of_chart_approximation
    hD O hrel happrox p (hcompact j) isClosed_frontier
  refine ⟨j, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv 1 zero_lt_one] with k hk q hq
  have hdist := hk q hq
  rw [hradius j q hq, Real.dist_eq] at hdist
  have hA : A ≤ dist (e k i₀ p) (F k q) := by
    have := (abs_lt.mp hdist).2
    linarith
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal hA

end PoincareConjecture.ChartDistance
