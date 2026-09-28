import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.CountableCharts
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Connectedness

set_option autoImplicit false

open Set Filter Metric
open scoped Topology NNReal Manifold ContDiff

universe u v

namespace PoincareConjecture.ChartDistance

theorem quotient_preconnected_of_regular_component_covers
    {ι : Type v} {X : ι → Type*} [∀ i, MetricSpace (X i)]
    {n : ℕ} {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {e : ∀ k i, X i → M k} {D : ∀ i j, C(X i × X j, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : X i × X j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)
    (O : Poincare.Gluing.OverlapSystem X)
    (hrel : ∀ i j (x : X i) (y : X j), O.Rel ⟨i, x⟩ ⟨j, y⟩ ↔ D i j (x, y) = 0)
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (g : ∀ k, RiemannianMetric n (M k)) (r : ℕ → ℝ)
    {i₀ : ι} (p : X i₀)
    (hcover : ∀ j, ∃ s : Finset ι, ∃ K : ∀ i, Set (X i),
      (∀ i ∈ s, IsCompact (K i)) ∧
        ∀ᶠ k in atTop, M28.regularComponent (g k) (e k i₀ p) (r j) ⊆
          ⋃ i ∈ s, e k i '' K i)
    (hregular : ∀ i (x : X i), ∃ j,
      ∀ᶠ k in atTop, e k i x ∈ M28.regularComponent (g k) (e k i₀ p) (r j)) :
    PreconnectedSpace (Quotient O.setoid) := by
  classical
  have hpoint := fun i j x y =>
    (hD i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  have hfull : ∀ S : Set (Quotient O.setoid), IsClopen S → O.include i₀ p ∈ S → S = univ := by
    intro S hS hp
    apply eq_univ_of_forall
    intro q
    induction q using Quotient.inductionOn with
    | h q =>
      by_contra hq
      obtain ⟨j, hqcomponent⟩ := hregular q.1 q.2
      obtain ⟨s, K, hK, hcov⟩ := hcover j
      let A := fun i => K i ∩ O.include i ⁻¹' S
      let B := fun i => K i ∩ O.include i ⁻¹' Sᶜ
      have hA (i) (hi : i ∈ s) : IsCompact (A i) :=
        (hK i hi).inter_right (hS.isClosed.preimage (O.include_isOpenEmbedding i).continuous)
      have hB (i) (hi : i ∈ s) : IsCompact (B i) :=
        (hK i hi).inter_right (hS.compl.isClosed.preimage (O.include_isOpenEmbedding i).continuous)
      let a := fun k => ⋃ i ∈ s, e k i '' A i
      let b := fun k => ⋃ i ∈ s, e k i '' B i
      have hdisj : ∀ᶠ k in atTop, Disjoint (a k) (b k) := by
        have hh : ∀ i ∈ s, ∀ᶠ k in atTop, ∀ l ∈ s,
            Disjoint (e k i '' A i) (e k l '' B l) := by
          intro i hi
          apply s.eventually_all.mpr
          intro l hl
          apply eventually_disjoint_source_images hD (hA i hi) (hB l hl)
          intro x hx y hy hzero
          have heq : O.include i x = O.include l y :=
            Quotient.sound ((hrel i l x y).mpr hzero)
          exact hy.2 (heq ▸ hx.2)
        filter_upwards [s.eventually_all.mpr hh] with k hk
        simp only [a, b, disjoint_iUnion_left, disjoint_iUnion_right]
        exact fun l hl i hi => hk i hi l hl
      have hnot (i : ι) (x : X i) (C : ∀ l, Set (X l))
          (hC : ∀ l ∈ s, IsCompact (C l))
          (hzero : ∀ l ∈ s, ∀ y ∈ C l, D i l (x, y) ≠ 0) :
          ∀ᶠ k in atTop, e k i x ∉ ⋃ l ∈ s, e k l '' C l := by
        apply not_frequently.mp
        intro hf
        simp only [mem_iUnion, exists_prop] at hf
        obtain ⟨l, hl, hfreq⟩ := s.frequently_exists.mp hf
        obtain ⟨y, hy, hz⟩ := exists_zero_of_frequently_mem_image hpoint L he (hC l hl) hfreq
        exact hzero l hl y hy hz
      have hpnot : ∀ᶠ k in atTop, e k i₀ p ∉ b k := by
        apply hnot i₀ p B hB
        intro l _ y hy hz
        have heq : O.include i₀ p = O.include l y :=
          Quotient.sound ((hrel i₀ l p y).mpr hz)
        exact hy.2 (heq ▸ hp)
      have hqnot : ∀ᶠ k in atTop, e k q.1 q.2 ∉ a k := by
        apply hnot q.1 q.2 A hA
        intro l _ y hy hz
        have heq : O.include q.1 q.2 = O.include l y :=
          Quotient.sound ((hrel q.1 l q.2 y).mpr hz)
        apply hq
        change O.include q.1 q.2 ∈ S
        rw [heq]
        exact hy.2
      obtain ⟨k, hcovk, hdisjk, hpk, hqk, hqcomponentk⟩ :=
        (hcov.and (hdisj.and (hpnot.and (hqnot.and hqcomponent)))).exists
      have hpcomponent : e k i₀ p ∈ M28.regularComponent (g k) (e k i₀ p) (r j) :=
        M28.mem_regularComponent (g k)
          (connectedComponentIn_nonempty_iff.mp ⟨e k q.1 q.2, hqcomponentk⟩)
      have hab : M28.regularComponent (g k) (e k i₀ p) (r j) ⊆ a k ∪ b k := by
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
      rcases isPreconnected_iff_subset_of_disjoint_closed.mp
        (M28.isPreconnected_regularComponent (g k) (e k i₀ p) (r j))
        (a k) (b k) haClosed hbClosed hab
        (by rw [hdisjk.inter_eq, inter_empty]) with ha | hb
      · exact hqk (ha hqcomponentk)
      · exact hpk (hb hpcomponent)
  apply preconnectedSpace_iff_clopen.mpr
  intro S hS
  by_cases hp : O.include i₀ p ∈ S
  · exact Or.inr (hfull S hS hp)
  · left
    have h := congrArg compl (hfull Sᶜ hS.compl hp)
    simpa only [compl_compl, compl_univ] using h

end PoincareConjecture.ChartDistance

namespace PoincareConjecture.M28

theorem regularChartQuotient_preconnected
    {n : ℕ} {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k}
    {δ R ρ : ℕ → ℝ} {N : ℕ → ℕ}
    (cover : ∀ k j, j ≤ k → RegularNormalChartCover (g k) (p k)
      (δ j) (R j) (ρ j) (N j))
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j)
    (hstep : ∀ j, 4 * δ (j + 1) ≤ 2 * δ j)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {D : ∀ _i _j : ℕ, C(ball (0 : EuclideanSpace ℝ (Fin n)) 1 ×
      ball (0 : EuclideanSpace ℝ (Fin n)) 1, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (x : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ×
        ball (0 : EuclideanSpace ℝ (Fin n)) 1) =>
        dist (regularUnitBallMap cover (φ k) i x.1)
          (regularUnitBallMap cover (φ k) j x.2)) (D i j) atTop)
    (O : Poincare.Gluing.OverlapSystem
      (fun _ : ℕ => ball (0 : EuclideanSpace ℝ (Fin n)) 1))
    (hrel : ∀ i j x y, O.Rel ⟨i, x⟩ ⟨j, y⟩ ↔ D i j (x, y) = 0)
    (L : ℕ → ℝ≥0)
    (he : ∀ k i, LipschitzWith (L i) (regularUnitBallMap cover (φ k) i)) :
    PreconnectedSpace (Quotient O.setoid) := by
  apply ChartDistance.quotient_preconnected_of_regular_component_covers hD O hrel L he
    (fun k => g (φ k)) (fun j => 4 * δ j) (i₀ := 0) ⟨0, by simp⟩
  · intro j
    obtain ⟨S, K, hK, hcover⟩ := regularUnitBallMap_compact_cover cover hρ j
    refine ⟨S, K, hK, ?_⟩
    simpa only [regularUnitBallMap_zero] using hφ.tendsto_atTop.eventually hcover
  · intro i x
    refine ⟨(Nat.unpair i).1 + 1, ?_⟩
    filter_upwards [hφ.tendsto_atTop.eventually
      (regularUnitBallMap_eventually_mem_regularComponent cover hρ hρR i)] with k hk
    rw [regularUnitBallMap_zero]
    exact regularComponent_antitone (g (φ k)) (p (φ k)) (hstep _) (hk x)

end PoincareConjecture.M28
