import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.NestedShellDisks

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)


theorem shell_half_complement_of_spanning_sides
    {S sq A U W L R : Set P2} {a b : P2}
    (hS : IsFinitePLBallPair P2 S sq)
    (hA : IsFinitePLBallPair P2 A (U ∪ ((L ∪ W) ∪ R)))
    (hD : IsFinitePLBallPair P2 (S ∩ A) (W ∪ (sq ∩ A)))
    (hW : IsFinitePLBallPair ℝ W {a, b})
    (hu : IsFinitePLBallPair ℝ (sq ∩ A) {a, b}) (hab : a ≠ b)
    (hproper : (sq ∩ A) \ {a, b} ⊆ A \ (U ∪ ((L ∪ W) ∪ R)))
    (hUS : Disjoint U S) (hLS : L ∩ S = {a}) (hRS : R ∩ S = {b})
    (hWS : W ⊆ S) (hLa : a ∈ L) (hRb : b ∈ R) :
    IsFinitePLBallPair P2 (A \ interior S) ((U ∪ (sq ∩ A)) ∪ (L ∪ R)) := by
  obtain ⟨V, _, hcover, hinter, hball, _⟩ :=
    hA.exists_boundary_attached_disk_complement hD inter_subset_right hW
      (fun z hz ↦ Or.inr (Or.inl (Or.inr hz))) hu hab hproper
  have hVL : V = (U ∪ L) ∪ R := by
    ext z
    constructor
    · intro hz
      rcases hcover.subset (Or.inr hz) with hzU | (hzL | hzW) | hzR
      · exact Or.inl (Or.inl hzU)
      · exact Or.inl (Or.inr hzL)
      · rcases hinter.subset ⟨hzW, hz⟩ with rfl | rfl
        · exact Or.inl (Or.inr hLa)
        · exact Or.inr hRb
      · exact Or.inr hzR
    · intro hz
      have hzrim : z ∈ U ∪ ((L ∪ W) ∪ R) := by
        rcases hz with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inr h)
      rcases hcover.symm.subset hzrim with hzW | hzV
      · have hends : z ∈ ({a, b} : Set P2) := by
          rcases hz with (h | h) | h
          · exact (disjoint_left.mp hUS h (hWS hzW)).elim
          · exact Or.inl (hLS.subset ⟨h, hWS hzW⟩)
          · exact Or.inr (hRS.subset ⟨h, hWS hzW⟩)
        exact (hinter.symm.subset hends).2
      · exact hzV
  have hset : A \ ((S ∩ A) \ (sq ∩ A)) = A \ interior S := by
    rw [hS.interior_eq_sdiff_of_finrank_eq rfl]
    ext z
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [hset, hVL] at hball
  convert hball using 1
  ext z
  simp only [mem_union, mem_inter_iff]
  tauto

end PoincareConjecture.M76.Dehn
