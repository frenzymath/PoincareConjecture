import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Gluing

set_option autoImplicit false
open Set Filter Metric
open scoped Topology NNReal

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {X : ι → Type*} [∀ i, MetricSpace (X i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {e : ∀ k i, X i → M k} {D : ∀ i j, X i × X j → ℝ}
    (hD : ∀ i j x y, Tendsto (fun k => dist (e k i x) (e k j y)) atTop
      (𝓝 (D i j (x, y))))
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))

include hD he

theorem exists_zero_of_frequently_mem_image
    {i j : ι} {x : X i} {K : Set (X j)} (hK : IsCompact K)
    (himage : ∃ᶠ k in atTop, e k i x ∈ e k j '' K) :
    ∃ y ∈ K, D i j (x, y) = 0 := by
  obtain ⟨k, y, hy, _⟩ := himage.exists
  obtain ⟨σ, hσ, hrep⟩ := subseq_forall_of_frequently
    (x := id) (p := fun k => e k i x ∈ e k j '' K) tendsto_id himage
  exact exists_zero_of_eventually_mem_image
    (M := fun k => M (σ k)) (e := fun k => e (σ k))
    (fun i j x y => (hD i j x y).comp hσ) L (fun k => he (σ k)) hK ⟨y, hy⟩
    (Eventually.of_forall hrep)

theorem exists_zero_of_eventually_mem_finite_images
    (s : Finset ι) (K : ∀ j, Set (X j)) (hK : ∀ j ∈ s, IsCompact (K j))
    {i : ι} {x : X i}
    (himage : ∀ᶠ k in atTop, ∃ j ∈ s, e k i x ∈ e k j '' K j) :
    ∃ j ∈ s, ∃ y ∈ K j, D i j (x, y) = 0 := by
  obtain ⟨j, hjs, hj⟩ := s.frequently_exists.mp himage.frequently
  obtain ⟨y, hy, hzero⟩ := exists_zero_of_frequently_mem_image hD L he (hK j hjs) hj
  exact ⟨j, hjs, y, hy, hzero⟩

theorem compact_cover_of_eventual_source_ball_cover
    (O : Poincare.Gluing.OverlapSystem X)
    (hrel : ∀ i j (x : X i) (y : X j), O.Rel ⟨i, x⟩ ⟨j, y⟩ ↔ D i j (x, y) = 0)
    (s : Finset ι) (K : ∀ j, Set (X j)) (hK : ∀ j ∈ s, IsCompact (K j))
    {i₀ : ι} (p : X i₀) (R : ℝ)
    (hcover : ∀ᶠ k in atTop, ball (e k i₀ p) R ⊆ ⋃ j ∈ s, e k j '' K j) :
    IsCompact (⋃ j ∈ s, O.include j '' K j) ∧
      ∀ i (x : X i), D i₀ i (p, x) < R →
        O.include i x ∈ ⋃ j ∈ s, O.include j '' K j := by
  constructor
  · exact s.finite_toSet.isCompact_biUnion fun j hj =>
      (hK j hj).image (O.include_isOpenEmbedding j).continuous
  · intro i x hx
    have hdist : ∀ᶠ k in atTop, dist (e k i x) (e k i₀ p) < R := by
      simpa only [dist_comm] using (hD i₀ i p x).eventually (gt_mem_nhds hx)
    have hrep : ∀ᶠ k in atTop, ∃ j ∈ s, e k i x ∈ e k j '' K j := by
      filter_upwards [hcover, hdist] with k hk hd
      simpa only [mem_iUnion, exists_prop] using hk hd
    obtain ⟨j, hjs, y, hy, hzero⟩ :=
      exists_zero_of_eventually_mem_finite_images hD L he s K hK hrep
    have heq : O.include i x = O.include j y := Quotient.sound ((hrel i j x y).mpr hzero)
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hjs, y, hy, heq.symm⟩⟩

end PoincareConjecture.ChartDistance
