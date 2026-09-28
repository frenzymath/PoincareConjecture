import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Connectedness

set_option autoImplicit false

open Set Filter Metric
open scoped Topology NNReal

namespace PoincareConjecture.ChartDistance

theorem quotient_preconnected_of_local_source_ball_covers
    {ι : Type*} {X : ι → Type*} [∀ i, MetricSpace (X i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {e : ∀ k i, X i → M k} {D : ∀ i j, C(X i × X j, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : X i × X j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (O : Poincare.Gluing.OverlapSystem X)
    (hrel : ∀ i j (x : X i) (y : X j), O.Rel ⟨i, x⟩ ⟨j, y⟩ ↔ D i j (x, y) = 0)
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    {i₀ : ι} (p : X i₀)
    (hcover : ∀ i (x : X i), ∃ R : ℝ, 0 < R ∧ D i₀ i (p, x) < R ∧
      ∃ s : Finset ι, ∃ K : ∀ j, Set (X j), (∀ j ∈ s, IsCompact (K j)) ∧
        ∀ᶠ k in atTop, ball (e k i₀ p) R ⊆ ⋃ j ∈ s, e k j '' K j) :
    PreconnectedSpace (Quotient O.setoid) := by
  classical
  have hpoint := fun i j x y =>
    (hD i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  have hfull : ∀ S : Set (Quotient O.setoid), IsClopen S → O.include i₀ p ∈ S →
      S = univ := by
    intro S hS hp
    apply eq_univ_of_forall
    intro q
    induction q using Quotient.inductionOn with
    | h q =>
      by_contra hq
      obtain ⟨R, hR, hqR, s, K, hK, hcov⟩ := hcover q.1 q.2
      let A := fun i => K i ∩ O.include i ⁻¹' S
      let B := fun i => K i ∩ O.include i ⁻¹' Sᶜ
      have hA (i) (hi : i ∈ s) : IsCompact (A i) :=
        (hK i hi).inter_right (hS.isClosed.preimage (O.include_isOpenEmbedding i).continuous)
      have hB (i) (hi : i ∈ s) : IsCompact (B i) :=
        (hK i hi).inter_right
          (hS.compl.isClosed.preimage (O.include_isOpenEmbedding i).continuous)
      let a := fun k => ⋃ i ∈ s, e k i '' A i
      let b := fun k => ⋃ i ∈ s, e k i '' B i
      have hdisj : ∀ᶠ k in atTop, Disjoint (a k) (b k) := by
        have hh : ∀ i ∈ s, ∀ᶠ k in atTop, ∀ j ∈ s,
            Disjoint (e k i '' A i) (e k j '' B j) := by
          intro i hi
          apply s.eventually_all.mpr
          intro j hj
          apply eventually_disjoint_source_images hD (hA i hi) (hB j hj)
          intro x hx y hy hzero
          have heq : O.include i x = O.include j y :=
            Quotient.sound ((hrel i j x y).mpr hzero)
          exact hy.2 (heq ▸ hx.2)
        filter_upwards [s.eventually_all.mpr hh] with k hk
        simp only [a, b, disjoint_iUnion_left, disjoint_iUnion_right]
        exact fun j hj i hi => hk i hi j hj
      have hnot (i : ι) (x : X i) (C : ∀ j, Set (X j))
          (hC : ∀ j ∈ s, IsCompact (C j))
          (hzero : ∀ j ∈ s, ∀ y ∈ C j, D i j (x, y) ≠ 0) :
          ∀ᶠ k in atTop, e k i x ∉ ⋃ j ∈ s, e k j '' C j := by
        apply not_frequently.mp
        intro hf
        simp only [mem_iUnion, exists_prop] at hf
        obtain ⟨j, hj, hfreq⟩ := s.frequently_exists.mp hf
        obtain ⟨y, hy, hz⟩ :=
          exists_zero_of_frequently_mem_image hpoint L he (hC j hj) hfreq
        exact hzero j hj y hy hz
      have hpnot : ∀ᶠ k in atTop, e k i₀ p ∉ b k := by
        apply hnot i₀ p B hB
        intro j _ y hy hz
        have heq : O.include i₀ p = O.include j y :=
          Quotient.sound ((hrel i₀ j p y).mpr hz)
        exact hy.2 (heq ▸ hp)
      have hqnot : ∀ᶠ k in atTop, e k q.1 q.2 ∉ a k := by
        apply hnot q.1 q.2 A hA
        intro j _ y hy hz
        have heq : O.include q.1 q.2 = O.include j y :=
          Quotient.sound ((hrel q.1 j q.2 y).mpr hz)
        apply hq
        change O.include q.1 q.2 ∈ S
        rw [heq]
        exact hy.2
      have hqball : ∀ᶠ k in atTop, e k q.1 q.2 ∈ ball (e k i₀ p) R := by
        simpa only [mem_ball, dist_comm] using
          (hpoint i₀ q.1 p q.2).eventually (gt_mem_nhds hqR)
      obtain ⟨k, hcovk, hdisjk, hpk, hqk, hqballk⟩ :=
        (hcov.and (hdisj.and (hpnot.and (hqnot.and hqball)))).exists
      have hab : ball (e k i₀ p) R ⊆ a k ∪ b k := by
        intro z hz
        obtain ⟨i, hi, x, hx, rfl⟩ := by
          simpa only [mem_iUnion, exists_prop, mem_image] using hcovk hz
        by_cases hxS : O.include i x ∈ S
        · exact Or.inl (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, x, ⟨hx, hxS⟩, rfl⟩⟩)
        · exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, x, ⟨hx, hxS⟩, rfl⟩⟩)
      have haClosed : IsClosed (a k) :=
        (s.finite_toSet.isCompact_biUnion fun i hi =>
          (hA i hi).image (he k i).continuous).isClosed
      have hbClosed : IsClosed (b k) :=
        (s.finite_toSet.isCompact_biUnion fun i hi =>
          (hB i hi).image (he k i).continuous).isClosed
      rcases isPreconnected_iff_subset_of_disjoint_closed.mp (hconn k (e k i₀ p) R)
        (a k) (b k) haClosed hbClosed hab
        (by rw [hdisjk.inter_eq, inter_empty]) with ha | hb
      · exact hqk (ha hqballk)
      · exact hpk (hb (mem_ball_self hR))
  apply preconnectedSpace_iff_clopen.mpr
  intro S hS
  by_cases hp : O.include i₀ p ∈ S
  · exact Or.inr (hfull S hS hp)
  · left
    have h := congrArg compl (hfull Sᶜ hS.compl hp)
    simpa only [compl_compl, compl_univ] using h

end PoincareConjecture.ChartDistance
