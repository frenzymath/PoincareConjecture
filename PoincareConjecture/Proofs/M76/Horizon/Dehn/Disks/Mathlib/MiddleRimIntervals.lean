import PoincareConjecture.Proofs.M76.Horizon.Dehn.Arcs.Mathlib.InteriorIntervalComplement
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripArmCharts











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn



theorem exists_middle_disk_old_rim_intervals
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M Q W Z : Set E} {a b u v : E}
    (hM : IsFinitePLBallPair (ℝ × ℝ) M (((M ∩ Q) ∪ W) ∪ Z))
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hZ : IsFinitePLBallPair ℝ Z {u, v})
    (hab : a ≠ b) (huv : u ≠ v) (hWZ : Disjoint W Z)
    (hWQ : W ∩ Q = {a, b}) (hZQ : Z ∩ Q = {u, v}) :
    ∃ (L R : Set E) (c d : E),
      ({c, d} : Set E) = {u, v} ∧ c ≠ d ∧
      IsFinitePLBallPair ℝ L {a, c} ∧ IsFinitePLBallPair ℝ R {d, b} ∧
      Disjoint L R ∧ L ∪ R = M ∩ Q ∧
      L ∩ W = {a} ∧ R ∩ W = {b} ∧ L ∩ Z = {c} ∧ R ∩ Z = {d} := by
  obtain ⟨J, hJ, hWJcover, hWJi⟩ := hM.exists_boundary_arc_complement hW
    (subset_union_right.trans subset_union_left) hab
  have hZJ : Z ⊆ J := by
    intro x hxZ
    rcases hWJcover.symm.subset (Or.inr hxZ) with hxW | hxJ
    · exact False.elim (Set.disjoint_left.mp hWZ hxW hxZ)
    · exact hxJ
  have hZends : Disjoint Z {a, b} := hWZ.symm.mono Subset.rfl hW.1
  obtain ⟨L, R, c, d, hpair, hcd, hL, hR, hLR, hJcover, hLZ, hZR⟩ :=
    exists_complementary_end_intervals hJ hZ hZJ hab huv hZends
  have hLJ : L ⊆ J := (subset_union_left.trans subset_union_left).trans hJcover.subset
  have hRJ : R ⊆ J := subset_union_right.trans hJcover.subset
  have hLa : a ∈ L := hL.1 (Or.inl rfl)
  have hRb : b ∈ R := hR.1 (Or.inr rfl)
  have hWa : a ∈ W := hW.1 (Or.inl rfl)
  have hWb : b ∈ W := hW.1 (Or.inr rfl)
  have hLW : L ∩ W = {a} := by
    ext x
    constructor
    · rintro ⟨hxL, hxW⟩
      rcases hWJi.subset ⟨hxW, hLJ hxL⟩ with hxa | hxb
      · exact hxa
      · exact False.elim (Set.disjoint_left.mp hLR hxL (hxb ▸ hRb))
    · rintro rfl
      exact ⟨hLa, hWa⟩
  have hRW : R ∩ W = {b} := by
    ext x
    constructor
    · rintro ⟨hxR, hxW⟩
      rcases hWJi.subset ⟨hxW, hRJ hxR⟩ with hxa | hxb
      · exact False.elim (Set.disjoint_left.mp hLR (hxa ▸ hLa) hxR)
      · exact hxb
    · rintro rfl
      exact ⟨hRb, hWb⟩
  have hRZ : R ∩ Z = {d} := by rwa [inter_comm] at hZR
  have hJM : J ⊆ M := (subset_union_right.trans hWJcover.subset).trans hM.1
  have hcQ : c ∈ Q := (hZQ.symm.subset (hpair.subset (Or.inl rfl))).2
  have hdQ : d ∈ Q := (hZQ.symm.subset (hpair.subset (Or.inr rfl))).2
  have hLQ : L ⊆ Q := by
    intro x hxL
    rcases hWJcover.subset (Or.inr (hLJ hxL)) with (hxQ | hxW) | hxZ
    · exact hxQ.2
    · exact (hWQ.symm.subset (hWJi.subset ⟨hxW, hLJ hxL⟩)).2
    · have heq : x = c := hLZ.subset ⟨hxL, hxZ⟩
      exact heq ▸ hcQ
  have hRQ : R ⊆ Q := by
    intro x hxR
    rcases hWJcover.subset (Or.inr (hRJ hxR)) with (hxQ | hxW) | hxZ
    · exact hxQ.2
    · exact (hWQ.symm.subset (hWJi.subset ⟨hxW, hRJ hxR⟩)).2
    · have heq : x = d := hRZ.subset ⟨hxR, hxZ⟩
      exact heq ▸ hdQ
  have hold : L ∪ R = M ∩ Q := by
    apply Subset.antisymm
    · rintro x (hxL | hxR)
      · exact ⟨hJM (hLJ hxL), hLQ hxL⟩
      · exact ⟨hJM (hRJ hxR), hRQ hxR⟩
    · intro x hxQ
      have hxJ : x ∈ J := by
        rcases hWJcover.symm.subset (Or.inl (Or.inl hxQ)) with hxW | hxJ
        · exact (hWJi.symm.subset (hWQ.subset ⟨hxW, hxQ.2⟩)).2
        · exact hxJ
      rcases hJcover.symm.subset hxJ with (hxL | hxZ) | hxR
      · exact Or.inl hxL
      · have hxend := hpair.symm.subset (hZQ.subset ⟨hxZ, hxQ.2⟩)
        rcases hxend with hxc | hxd
        · exact Or.inl (hxc ▸ hL.1 (Or.inr rfl))
        · exact Or.inr (hxd ▸ hR.1 (Or.inl rfl))
      · exact Or.inr hxR
  exact ⟨L, R, c, d, hpair, hcd, hL, hR, hLR, hold, hLW, hRW, hLZ, hRZ⟩

end PoincareConjecture.M76.Dehn
