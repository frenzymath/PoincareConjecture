import PoincareConjecture.Proofs.M76.Horizon.Dehn.Arcs.Mathlib.InteriorIntervalComplement
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.TwoProperArcCuts

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_retained_disk_rim_intervals
    {E Q₀ Q₁ W₀ W₁ : Set P2} {a₀ b₀ a₁ b₁ : P2}
    (hE : IsFinitePLBallPair P2 E (((E ∩ (Q₀ ∪ Q₁)) ∪ W₀) ∪ W₁))
    (hW₀ : IsFinitePLBallPair ℝ W₀ {a₀, b₀})
    (hW₁ : IsFinitePLBallPair ℝ W₁ {a₁, b₁})
    (hdisW : Disjoint W₀ W₁) (hQ₀ : IsClosed Q₀) (hQ₁ : IsClosed Q₁)
    (hdisQ : Disjoint Q₀ Q₁)
    (hW₀Q₀ : W₀ ∩ Q₀ = {a₀}) (hW₀Q₁ : W₀ ∩ Q₁ = {b₀})
    (hW₁Q₀ : W₁ ∩ Q₀ = {a₁}) (hW₁Q₁ : W₁ ∩ Q₁ = {b₁}) :
    IsFinitePLBallPair ℝ (E ∩ Q₀) {a₀, a₁} ∧
      IsFinitePLBallPair ℝ (E ∩ Q₁) {b₀, b₁} := by
  have ha₀ : a₀ ∈ Q₀ := (hW₀Q₀.symm.subset rfl).2
  have hb₀ : b₀ ∈ Q₁ := (hW₀Q₁.symm.subset rfl).2
  have ha₁ : a₁ ∈ Q₀ := (hW₁Q₀.symm.subset rfl).2
  have hb₁ : b₁ ∈ Q₁ := (hW₁Q₁.symm.subset rfl).2
  have hab₀ : a₀ ≠ b₀ := fun h ↦ disjoint_left.mp hdisQ ha₀ (h ▸ hb₀)
  have hab₁ : a₁ ≠ b₁ := fun h ↦ disjoint_left.mp hdisQ ha₁ (h ▸ hb₁)
  obtain ⟨V, hV, hW₀V, hinter⟩ := hE.exists_boundary_arc_complement hW₀
    (fun _ h ↦ Or.inl (Or.inr h)) hab₀
  have hW₁V : W₁ ⊆ V := by
    intro x hx
    rcases hW₀V.symm.subset (Or.inr hx) with hx₀ | hxV
    · exact (disjoint_left.mp hdisW hx₀ hx).elim
    · exact hxV
  have hends : Disjoint W₁ ({a₀, b₀} : Set P2) := hdisW.symm.mono_right hW₀.1
  obtain ⟨L, R, c, d, hpair, _, hL, hR, hLR, hcover, hLW₁, hW₁R⟩ :=
    exists_complementary_end_intervals hV hW₁ hW₁V hab₀ hab₁ hends
  have hLV : L ⊆ V := (subset_union_left.trans subset_union_left).trans hcover.subset
  have hRV : R ⊆ V := subset_union_right.trans hcover.subset
  have hLq : L ⊆ ((E ∩ (Q₀ ∪ Q₁)) ∪ W₀) ∪ W₁ :=
    hLV.trans (subset_union_right.trans hW₀V.subset)
  have hRq : R ⊆ ((E ∩ (Q₀ ∪ Q₁)) ∪ W₀) ∪ W₁ :=
    hRV.trans (subset_union_right.trans hW₀V.subset)
  have ha₀L : a₀ ∈ L := hL.1 (Or.inl rfl)
  have hb₀R : b₀ ∈ R := hR.1 (Or.inr rfl)
  have hLW₀ : L ∩ W₀ = {a₀} := by
    apply Subset.antisymm
    · intro x hx
      rcases hinter.subset ⟨hx.2, hLV hx.1⟩ with he | he
      · exact he
      · exact (disjoint_left.mp hLR hx.1 (he ▸ hb₀R)).elim
    · rintro x rfl
      exact ⟨ha₀L, hW₀.1 (Or.inl rfl)⟩
  have hRW₀ : R ∩ W₀ = {b₀} := by
    apply Subset.antisymm
    · intro x hx
      rcases hinter.subset ⟨hx.2, hRV hx.1⟩ with he | he
      · exact (disjoint_left.mp hLR (he ▸ ha₀L) hx.1).elim
      · exact he
    · rintro x rfl
      exact ⟨hb₀R, hW₀.1 (Or.inr rfl)⟩
  have hcQ : c ∈ Q₀ ∪ Q₁ := by
    rcases hpair.subset (Or.inl rfl) with h | h
    · exact Or.inl (h ▸ ha₁)
    · exact Or.inr (h ▸ hb₁)
  have hdQ : d ∈ Q₀ ∪ Q₁ := by
    rcases hpair.subset (Or.inr rfl) with h | h
    · exact Or.inl (h ▸ ha₁)
    · exact Or.inr (h ▸ hb₁)
  have hLQ : L ⊆ Q₀ ∪ Q₁ := by
    intro x hx
    rcases hLq hx with (hxQ | hxW) | hxW
    · exact hxQ.2
    · exact Or.inl ((hLW₀.subset ⟨hx, hxW⟩) ▸ ha₀)
    · exact (hLW₁.subset ⟨hx, hxW⟩) ▸ hcQ
  have hRQ : R ⊆ Q₀ ∪ Q₁ := by
    intro x hx
    rcases hRq hx with (hxQ | hxW) | hxW
    · exact hxQ.2
    · exact Or.inr ((hRW₀.subset ⟨hx, hxW⟩) ▸ hb₀)
    · exact (hW₁R.subset ⟨hxW, hx⟩) ▸ hdQ
  have hLQ₀ : L ⊆ Q₀ := by
    rcases isPreconnected_subset_one_cut_piece hL.isConnected.isPreconnected hQ₀ hQ₁
      hLQ hdisQ.inter_eq (disjoint_empty _) with h | h
    · exact h
    · exact (disjoint_left.mp hdisQ ha₀ (h ha₀L)).elim
  have hRQ₁ : R ⊆ Q₁ := by
    rcases isPreconnected_subset_one_cut_piece hR.isConnected.isPreconnected hQ₀ hQ₁
      hRQ hdisQ.inter_eq (disjoint_empty _) with h | h
    · exact (disjoint_left.mp hdisQ (h hb₀R) hb₀).elim
    · exact h
  have hc : c = a₁ := by
    rcases hpair.subset (Or.inl rfl) with h | h
    · exact h
    · exact (disjoint_left.mp hdisQ (hLQ₀ (hL.1 (Or.inr rfl))) (h ▸ hb₁)).elim
  have hd : d = b₁ := by
    rcases hpair.subset (Or.inr rfl) with h | h
    · exact (disjoint_left.mp hdisQ (h ▸ ha₁) (hRQ₁ (hR.1 (Or.inl rfl)))).elim
    · exact h
  subst c d
  have hLE : L = E ∩ Q₀ := by
    apply Subset.antisymm (show L ⊆ E ∩ Q₀ from fun _ hx ↦ ⟨hE.1 (hLq hx), hLQ₀ hx⟩)
    intro x hx
    rcases hW₀V.symm.subset (Or.inl (Or.inl ⟨hx.1, Or.inl hx.2⟩)) with hxW | hxV
    · have he := hW₀Q₀.subset ⟨hxW, hx.2⟩
      exact he ▸ ha₀L
    · rcases hcover.symm.subset hxV with (hxL | hxW) | hxR
      · exact hxL
      · exact (hW₁Q₀.subset ⟨hxW, hx.2⟩) ▸ hL.1 (Or.inr rfl)
      · exact (disjoint_left.mp hdisQ hx.2 (hRQ₁ hxR)).elim
  have hRE : R = E ∩ Q₁ := by
    apply Subset.antisymm (show R ⊆ E ∩ Q₁ from fun _ hx ↦ ⟨hE.1 (hRq hx), hRQ₁ hx⟩)
    intro x hx
    rcases hW₀V.symm.subset (Or.inl (Or.inl ⟨hx.1, Or.inr hx.2⟩)) with hxW | hxV
    · exact (hW₀Q₁.subset ⟨hxW, hx.2⟩) ▸ hb₀R
    · rcases hcover.symm.subset hxV with (hxL | hxW) | hxR
      · exact (disjoint_left.mp hdisQ (hLQ₀ hxL) hx.2).elim
      · exact (hW₁Q₁.subset ⟨hxW, hx.2⟩) ▸ hR.1 (Or.inl rfl)
      · exact hxR
  exact ⟨hLE ▸ hL, hRE ▸ (by simpa only [pair_comm] using hR)⟩

end PoincareConjecture.M76.Dehn
