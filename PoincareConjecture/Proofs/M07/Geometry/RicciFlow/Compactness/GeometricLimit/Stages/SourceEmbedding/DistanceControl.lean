import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.BoundaryEscape
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.DistanceMetric

set_option autoImplicit false
open Set Filter Metric
open scoped Topology

namespace PoincareConjecture.ChartDistance

theorem tendstoUniformlyOn_chart_approximation_of_local_charts
    {ι : Type*} {X : ι → Type*} [∀ i, MetricSpace (X i)]
    [∀ i, LocallyCompactSpace (X i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {e : ∀ k i, X i → M k} {D : ∀ i j, C(X i × X j, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : X i × X j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (O : Poincare.Gluing.OverlapSystem X)
    (hrel : ∀ i j (x : X i) (y : X j), O.Rel ⟨i, x⟩ ⟨j, y⟩ ↔ D i j (x, y) = 0)
    {V : Set (Quotient O.setoid)} (hV : IsOpen V) {F : ∀ k, Quotient O.setoid → M k}
    (hlocal : ∀ q ∈ V, ∃ j, ∃ B : Set (X j), IsOpen B ∧ q ∈ O.include j '' B ∧
      ∀ C, IsCompact C → C ⊆ B → TendstoUniformlyOn
        (fun k y => dist (F k (O.include j y)) (e k j y)) (fun _ => 0) atTop C)
    (i : ι) {K : Set (X i)} (hK : IsCompact K) (hKV : O.include i '' K ⊆ V) :
    TendstoUniformlyOn (fun k x => dist (F k (O.include i x)) (e k i x))
      (fun _ => 0) atTop K := by
  have hVi : IsOpen (O.include i ⁻¹' V) := hV.preimage (O.include_isOpenEmbedding i).continuous
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hVi).mp ?_ K
    (image_subset_iff.mp hKV) hK
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro x hx
  obtain ⟨j, B, hB, hxB, hBj⟩ := hlocal (O.include i x) hx
  let W := O.include i ⁻¹' (O.include j '' B)
  have hW : IsOpen W := (O.include_isOpenMap j _ hB).preimage
    (O.include_isOpenEmbedding i).continuous
  obtain ⟨C, ⟨hCn, hC⟩, hCW⟩ := (compact_basis_nhds x).mem_iff.mp (hW.mem_nhds hxB)
  have hCsource : C ⊆ (O.transition i j).source := by
    intro y hy
    have h := hCW hy
    change y ∈ O.include i ⁻¹' (O.include j '' B) at h
    rw [O.include_preimage_image] at h
    exact h.1
  have hCB : O.transition i j '' C ⊆ B := by
    rintro _ ⟨y, hy, rfl⟩
    have h := hCW hy
    change y ∈ O.include i ⁻¹' (O.include j '' B) at h
    rw [O.include_preimage_image] at h
    exact h.2
  have hCt := hC.image_of_continuousOn ((O.transition i j).continuousOn.mono hCsource)
  refine ⟨C, nhdsWithin_le_nhds hCn, ?_⟩
  apply tendstoUniformlyOn_chart_approximation_of_finite_cover hD O hrel
    (Finset.univ : Finset Unit) (fun _ => j) (fun _ => O.transition i j '' C)
    (fun _ _ => hCt) (fun _ _ => hBj _ hCt hCB) hC
  rintro _ ⟨y, hy, rfl⟩
  apply mem_iUnion.mpr
  refine ⟨(), mem_iUnion.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  exact ⟨O.transition i j y, mem_image_of_mem _ hy,
    ((O.include_eq_iff i j _ _).mpr ⟨hCsource hy, rfl⟩).symm⟩

theorem tendstoUniformlyOn_source_chart_distance_of_approximation
    {ι : Type*} {X : ι → Type*} [∀ i, MetricSpace (X i)]
    [∀ i, WeaklyLocallyCompactSpace (X i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {e : ∀ k i, X i → M k} {D : ∀ i j, C(X i × X j, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : X i × X j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (O : Poincare.Gluing.OverlapSystem X)
    (hrel : ∀ i j (x : X i) (y : X j), O.Rel ⟨i, x⟩ ⟨j, y⟩ ↔ D i j (x, y) = 0)
    {V : Set (Quotient O.setoid)} {F : ∀ k, Quotient O.setoid → M k}
    (happrox : ∀ i K, IsCompact K → O.include i '' K ⊆ V → TendstoUniformlyOn
      (fun k x => dist (F k (O.include i x)) (e k i x)) (fun _ => 0) atTop K)
    {A : Set (Quotient O.setoid)} (hA : IsCompact A) (hAc : IsClosed A) (hAV : A ⊆ V)
    {j : ι} {C : Set (X j)} (hC : IsCompact C) :
    TendstoUniformlyOn (fun k (p : Quotient O.setoid × X j) => dist (F k p.1) (e k j p.2))
      (fun p => quotientDistance
        (fun i j x y => (hD i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y)))
        O hrel p.1 (O.include j p.2)) atTop (A ×ˢ C) := by
  obtain ⟨s, K, hK, hcover⟩ := exists_finite_compact_representatives O hA hAc
  have hKV (a : Σ i, X i) (ha : a ∈ s) : O.include a.1 '' K a ⊆ V := by
    intro q hq
    apply hAV
    rw [← hcover]
    exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨ha, hq⟩⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have herr := s.eventually_all.mpr fun a ha => Metric.tendstoUniformlyOn_iff.mp
    (happrox a.1 (K a) (hK a ha) (hKV a ha)) (ε / 2) (by positivity)
  have hdist := s.eventually_all.mpr fun a ha =>
    eventually_dist_sub_limit_lt_on_compact hD (K a ×ˢ C) ((hK a ha).prod hC)
      (show 0 < ε / 2 by positivity)
  filter_upwards [herr, hdist] with k hkF hkD p hp
  obtain ⟨a, ha, x, hx, hqx⟩ := by
    simpa only [← hcover, mem_iUnion, exists_prop, mem_image] using hp.1
  have hd : dist (D a.1 j (x, p.2)) (dist (e k a.1 x) (e k j p.2)) < ε / 2 := by
    simpa only [Real.dist_eq, abs_sub_comm] using hkD a ha (x, p.2) ⟨hx, hp.2⟩
  have hf : dist (F k (O.include a.1 x)) (e k a.1 x) < ε / 2 := by
    simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg dist_nonneg] using hkF a ha x hx
  rw [← hqx]
  change dist (D a.1 j (x, p.2)) (dist (F k (O.include a.1 x)) (e k j p.2)) < ε
  calc
    _ ≤ dist (D a.1 j (x, p.2)) (dist (e k a.1 x) (e k j p.2)) +
        dist (dist (e k a.1 x) (e k j p.2))
          (dist (F k (O.include a.1 x)) (e k j p.2)) := dist_triangle _ _ _
    _ ≤ dist (D a.1 j (x, p.2)) (dist (e k a.1 x) (e k j p.2)) +
        dist (F k (O.include a.1 x)) (e k a.1 x) := by
      gcongr
      simpa only [dist_self, add_zero, dist_comm] using
        dist_dist_dist_le (e k a.1 x) (e k j p.2) (F k (O.include a.1 x)) (e k j p.2)
    _ < ε := by linarith

end PoincareConjecture.ChartDistance
