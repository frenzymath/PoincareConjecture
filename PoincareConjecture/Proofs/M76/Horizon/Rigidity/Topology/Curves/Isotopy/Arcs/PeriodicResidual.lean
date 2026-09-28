import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.ResidualDecomposition
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.TranslatedComponents

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_complete_residual_of_finite_window
    (Q : ℤ → ℝ → P2) (hQ : ∀ j, FinitePiecewiseAffineOn (Q j) (Icc 0 1))
    (hdis : Pairwise fun i j => Disjoint (Q i '' Icc (0 : ℝ) 1) (Q j '' Icc (0 : ℝ) 1))
    (k : ℤ) (hi : InjOn (Q k) (Icc 0 1))
    {u v : ℝ} (huv : u < v) (hpositive : ∀ x ∈ Ioo u v, 0 < (Q k x).2)
    (hleft : ∃ a b m : ℝ, 0 ≤ a ∧ a < u ∧ u < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
      ∀ x ∈ Icc a b, (Q k x).2 - 0 = m * (x - u))
    (hright : ∃ a b m : ℝ, 0 ≤ a ∧ a < v ∧ v < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
      ∀ x ∈ Icc a b, (Q k x).2 - 0 = m * (x - v))
    {B U : Set P2} (hB : B ∩ (⋃ j : ℤ, Q j '' Icc (0 : ℝ) 1) = Q k '' Icc u v)
    (K : Finset ℤ)
    (hcapture : ∀ j s, s ∈ Icc (0 : ℝ) 1 → Q j s ∈ U → j ∈ K) :
    ∃ (l t : ℝ) (T : SimplicialComplex ℝ P2) (E : Set P2),
      0 < l ∧ l < u ∧ v < t ∧ t < 1 ∧ T.faces.Finite ∧
      T.space = Q k '' Icc l u ∪ Q k '' Icc v t ∧
      (∀ x ∈ T.space, x.2 ≤ 0) ∧
      (∀ x ∈ T.space, x.2 = 0 → x = Q k u ∨ x = Q k v) ∧
      (∃ m n : ℝ, 0 < m ∧ n < 0 ∧
        (∀ s ∈ Icc l u, (Q k s).2 = m * (s - u)) ∧
        (∀ s ∈ Icc v t, (Q k s).2 = n * (s - v))) ∧
      IsCompact E ∧ Disjoint B E ∧
      E = (Q k '' Icc 0 l ∪ Q k '' Icc t 1) ∪
        (⋃ j ∈ K.erase k, Q j '' Icc (0 : ℝ) 1) ∧
      E ⊆ (⋃ j : ℤ, Q j '' Icc (0 : ℝ) 1) \ (Q k '' Ioo u v) ∧
      ((⋃ j : ℤ, Q j '' Icc (0 : ℝ) 1) ∩ U) \ (Q k '' Ioo u v) ⊆ T.space ∪ E := by
  classical
  have hu : 0 < u := by obtain ⟨a, b, m, ha, hau, _⟩ := hleft; exact ha.trans_lt hau
  have hv : v < 1 := by
    obtain ⟨a, b, m, _, _, hvb, hb, _⟩ := hright
    exact hvb.trans_le hb
  have hsub : Icc u v ⊆ Icc (0 : ℝ) 1 :=
    fun y hy => ⟨hu.le.trans hy.1, hy.2.trans hv.le⟩
  have hBq : B ∩ (Q k '' Icc (0 : ℝ) 1) = Q k '' Icc u v := by
    apply Subset.antisymm
    · exact fun x hx => hB.subset ⟨hx.1, mem_iUnion.mpr ⟨k, hx.2⟩⟩
    · intro x hx
      exact ⟨(hB.symm.subset hx).1, image_mono hsub hx⟩
  obtain ⟨l, t, T, E₀, hl, hlu, hvt, ht, hT, hTs, hlower, haxis, hslopes,
    hE₀, hBE₀, hE₀s, hcover⟩ := exists_lower_tail_complex_and_distant_remainder
      (hQ k) hi huv hpositive hleft hright hBq
  let E₁ := ⋃ j ∈ K.erase k, Q j '' Icc (0 : ℝ) 1
  have hE₁ : IsCompact E₁ := (K.erase k).isCompact_biUnion fun j _ =>
    isCompact_Icc.image_of_continuousOn (hQ j).continuousOn
  have hBE₁ : Disjoint B E₁ := by
    apply disjoint_left.mpr
    intro x hxB hxE
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxE
    have hxk := hB.subset ⟨hxB, mem_iUnion.mpr ⟨j, hxj⟩⟩
    exact disjoint_left.mp (hdis (Finset.mem_erase.mp hj).1) hxj
      (image_mono hsub hxk)
  refine ⟨l, t, T, E₀ ∪ E₁, hl, hlu, hvt, ht, hT, hTs, hlower, haxis,
    hslopes, hE₀.union hE₁, disjoint_union_right.mpr ⟨hBE₀, hBE₁⟩,
    by rw [hE₀s], ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · rw [hE₀s] at hx
      rcases hx with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
      · have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans (hlu.trans (huv.trans hv)).le⟩
        refine ⟨mem_iUnion.mpr ⟨k, mem_image_of_mem (Q k) hsI⟩, ?_⟩
        rintro ⟨y, hy, hys⟩
        have he := hi (hsub (Ioo_subset_Icc_self hy)) hsI hys
        linarith [hy.1, hs.2]
      · have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨(hu.trans (huv.trans hvt)).le.trans hs.1, hs.2⟩
        refine ⟨mem_iUnion.mpr ⟨k, mem_image_of_mem (Q k) hsI⟩, ?_⟩
        rintro ⟨y, hy, hys⟩
        have he := hi (hsub (Ioo_subset_Icc_self hy)) hsI hys
        linarith [hy.2, hs.1]
    · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
      refine ⟨mem_iUnion.mpr ⟨j, hxj⟩, ?_⟩
      intro hxk
      exact disjoint_left.mp (hdis (Finset.mem_erase.mp hj).1) hxj
        (image_mono (Ioo_subset_Icc_self.trans hsub) hxk)
  rintro x ⟨⟨hx, hxU⟩, hxout⟩
  obtain ⟨j, s, hs, rfl⟩ := mem_iUnion.mp hx
  by_cases hj : j = k
  · subst j
    have hsout : s ∉ Ioo u v := fun h => hxout (mem_image_of_mem (Q k) h)
    rcases hcover (mem_image_of_mem (Q k) ⟨hs, hsout⟩) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (mem_iUnion₂.mpr
      ⟨j, Finset.mem_erase.mpr ⟨hj, hcapture j s hs hxU⟩, mem_image_of_mem (Q j) hs⟩))

theorem exists_narrow_periodic_window {r : ℝ → P2}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) {c d : ℝ} (hd : d < 32)
    {B : Set P2} (hB : B ⊆ Ioo (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) d) :
    ∃ (ε : ℝ) (K : Finset ℤ), 0 < ε ∧ d + 2 * ε < 32 ∧
      B ⊆ Ioo (-1 : ℝ) 1 ×ˢ Ioo (-ε) (d + ε) ∧
      ∀ (j : ℤ) (s : ℝ), s ∈ Icc (0 : ℝ) 1 →
        annularLiftAboveAxis r (c + 32 * (j : ℝ)) s ∈
          Ioo (-1 : ℝ) 1 ×ˢ Ioo (-ε) (d + ε) → j ∈ K := by
  classical
  let ε := (32 - d) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  let K := (finite_annular_translates_meeting_strip hr (c - ε) (d + 2 * ε)).toFinset
  refine ⟨ε, K, hε, by dsimp [ε]; linarith, ?_, ?_⟩
  · intro x hx
    have hh := hB hx
    exact ⟨hh.1, by linarith [hh.2.1], by linarith [hh.2.2]⟩
  · intro j s hs hx
    apply (finite_annular_translates_meeting_strip hr (c - ε) (d + 2 * ε)).mem_toFinset.mpr
    refine ⟨s, hs, ?_⟩
    have hx := hx.2
    change -ε < (r s).1 - (c + 32 * (j : ℝ)) ∧
      (r s).1 - (c + 32 * (j : ℝ)) < d + ε at hx
    constructor <;> linarith [hx.1, hx.2]

end PoincareConjecture.M76.Dehn
