import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryAttachedDisk











set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Dehn




theorem two_boundary_attached_disks_complement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S Q : Set E} (hS : IsFinitePLBallPair (ℝ × ℝ) S Q)
    (D U W : Bool → Set E) (a b : Bool → E)
    (hD : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (D i) (U i ∪ W i))
    (hDS : ∀ i, D i ⊆ S)
    (hU : ∀ i, IsFinitePLBallPair ℝ (U i) {a i, b i}) (hUQ : ∀ i, U i ⊆ Q)
    (hW : ∀ i, IsFinitePLBallPair ℝ (W i) {a i, b i}) (hab : ∀ i, a i ≠ b i)
    (hproper : ∀ i, W i \ {a i, b i} ⊆ S \ Q)
    (hdisj : Disjoint (D false) (D true)) :
    let C := S \ ((D false \ W false) ∪ (D true \ W true))
    IsFinitePLBallPair (ℝ × ℝ) C (((C ∩ Q) ∪ W false) ∪ W true) ∧
      (D false ∪ D true) ∪ C = S ∧ ∀ i, D i ∩ C = W i := by
  obtain ⟨V0, _, hQV0, _, hC0, hcover0, hinter0, _, hcontact0⟩ :=
    hS.exists_boundary_attached_disk_complement (hD false) (hDS false)
      (hU false) (hUQ false) (hW false) (hab false) (hproper false)
  let C0 := S \ (D false \ W false)
  have hWD (i : Bool) : W i ⊆ D i := subset_union_right.trans (hD i).1
  have hD1C0 : D true ⊆ C0 := by
    intro x hx
    exact ⟨hDS true hx, fun h => Set.disjoint_left.mp hdisj h.1 hx⟩
  have hU1Q0 : U true ⊆ W false ∪ V0 := by
    intro x hx
    exact Or.inr (hcontact0.subset ⟨hD1C0 ((hD true).1 (Or.inl hx)), hUQ true hx⟩)
  have hproper1 : W true \ {a true, b true} ⊆ C0 \ (W false ∪ V0) := by
    intro x hx
    refine ⟨hD1C0 (hWD true hx.1), ?_⟩
    rintro (hxW | hxV)
    · exact Set.disjoint_left.mp hdisj (hWD false hxW) (hWD true hx.1)
    · exact (hproper true hx).2 (hQV0.subset (Or.inr hxV))
  obtain ⟨V1, _, _, _, hC1, hcover1, hinter1, _, hcontact1⟩ :=
    hC0.exists_boundary_attached_disk_complement (hD true) hD1C0
      (hU true) hU1Q0 (hW true) (hab true) hproper1
  let C1 := C0 \ (D true \ W true)
  have hW0C1 : W false ⊆ C1 := by
    intro x hx
    exact ⟨hC0.1 (Or.inl hx), fun h => Set.disjoint_left.mp hdisj (hWD false hx) h.1⟩
  have hV1 : V1 = W false ∪ (C1 ∩ Q) := by
    rw [← hcontact1]
    ext x
    constructor
    · rintro ⟨hxC, hxW | hxV⟩
      · exact Or.inl hxW
      · exact Or.inr ⟨hxC, (hcontact0.symm.subset hxV).2⟩
    · rintro (hxW | ⟨hxC, hxQ⟩)
      · exact ⟨hW0C1 hxW, Or.inl hxW⟩
      · exact ⟨hxC, Or.inr (hcontact0.subset ⟨hxC.1, hxQ⟩)⟩
  have hC1full : IsFinitePLBallPair (ℝ × ℝ) C1 (((C1 ∩ Q) ∪ W false) ∪ W true) := by
    simpa only [hV1, union_assoc, union_left_comm, union_comm] using hC1
  have hD0contact : D false ∩ C1 = W false := by
    apply Subset.antisymm
    · exact fun x hx => hinter0.subset ⟨hx.1, hx.2.1⟩
    · exact fun x hx => ⟨hWD false hx, hW0C1 hx⟩
  have hcover : (D false ∪ D true) ∪ C1 = S := by
    rw [union_assoc, hcover1, hcover0]
  have hactual : C1 = S \ ((D false \ W false) ∪ (D true \ W true)) := by
    ext x
    change ((x ∈ S ∧ ¬ (x ∈ D false ∧ x ∉ W false)) ∧
      ¬ (x ∈ D true ∧ x ∉ W true)) ↔
      x ∈ S ∧ ¬ ((x ∈ D false ∧ x ∉ W false) ∨ (x ∈ D true ∧ x ∉ W true))
    tauto
  rw [← hactual]
  refine ⟨hC1full, hcover, ?_⟩
  intro i
  cases i with
  | false => exact hD0contact
  | true => exact hinter1

end PoincareConjecture.M76.Dehn
