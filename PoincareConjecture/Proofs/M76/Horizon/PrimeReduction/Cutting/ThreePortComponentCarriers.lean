import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.TwoPortComponentCarriers









set_option autoImplicit false
open Set

namespace Topology

theorem componentIn_closed_finite_port_attachment
    {X J : Type*} [TopologicalSpace X] [Finite J]
    {P D : Set X} [LocallyConnectedSpace P]
    (hP : IsClosed P) (hD : IsClosed D) (hDc : IsConnected D)
    (p : J → Set X) (hp : ∀ i, IsConnected (p i))
    (hports : P ∩ D = ⋃ i, p i) (a : J → X) (ha : ∀ i, a i ∈ p i) (i : J) :
    connectedComponentIn (P ∪ D) (a i) =
      (⋃ j, connectedComponentIn P (a j)) ∪ D ∧
    ∀ x ∈ P, x ∉ ⋃ j, connectedComponentIn P (a j) →
      connectedComponentIn (P ∪ D) x = connectedComponentIn P x := by
  classical
  have hpP (j : J) : p j ⊆ P :=
    (subset_iUnion p j).trans (hports.symm.subset.trans inter_subset_left)
  have haPD (j : J) : a j ∈ P ∩ D :=
    hports.symm.subset (mem_iUnion.mpr ⟨j, ha j⟩)
  let A := ⋃ j, connectedComponentIn P (a j)
  have hattach : P ∩ D ⊆ A := by
    rw [hports]
    apply iUnion_mono
    intro j
    exact (hp j).isPreconnected.subset_connectedComponentIn (ha j) (hpP j)
  have hAclosed : IsClosed A := by
    apply isClosed_iUnion_of_finite
    intro j
    rw [connectedComponentIn_eq_image (haPD j).1]
    exact hP.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hBclosed : IsClosed (P \ A) := by
    have heq : (Subtype.val : P → X) ''
        (⋃ j, connectedComponent (⟨a j, (haPD j).1⟩ : P))ᶜ = P \ A := by
      rw [image_compl_eq_range_sdiff_image Subtype.val_injective,
        Subtype.range_val, image_iUnion]
      congr 1
      apply iUnion_congr
      intro j
      exact (connectedComponentIn_eq_image (haPD j).1).symm
    rw [← heq]
    exact hP.isClosedMap_subtype_val _
      (isOpen_iUnion (fun _ => isOpen_connectedComponent)).isClosed_compl
  have hcover : P ∪ D ⊆ (A ∪ D) ∪ (P \ A) := by
    rintro x (hx | hx)
    · by_cases hxA : x ∈ A
      · exact Or.inl (Or.inl hxA)
      · exact Or.inr ⟨hx, hxA⟩
    · exact Or.inl (Or.inr hx)
  have hsep : Disjoint (A ∪ D) (P \ A) := by
    apply disjoint_left.mpr
    rintro x (hxA | hxD) hx
    · exact hx.2 hxA
    · exact hx.2 (hattach ⟨hx.1, hxD⟩)
  have hupper : connectedComponentIn (P ∪ D) (a i) ⊆ A ∪ D := by
    have h := isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_connectedComponentIn (F := P ∪ D) (x := a i))
      (A ∪ D) (P \ A) (hAclosed.union hD) hBclosed
      ((connectedComponentIn_subset _ _).trans hcover)
      (by rw [hsep.inter_eq, inter_empty])
    rcases h with h | h
    · exact h
    · exact False.elim ((h (mem_connectedComponentIn (Or.inl (haPD i).1))).2
        (mem_iUnion.mpr ⟨i, mem_connectedComponentIn (haPD i).1⟩))
  have hDa : D ⊆ connectedComponentIn (P ∪ D) (a i) :=
    hDc.isPreconnected.subset_connectedComponentIn (haPD i).2 subset_union_right
  have heq : connectedComponentIn (P ∪ D) (a i) = A ∪ D := by
    apply Subset.antisymm hupper
    apply union_subset _ hDa
    apply iUnion_subset
    intro j
    have hji := hDa (haPD j).2
    have hsub := connectedComponentIn_mono (a j) (show P ⊆ P ∪ D from subset_union_left)
    rwa [connectedComponentIn_eq hji] at *
  refine ⟨heq, ?_⟩
  intro x hx hxA
  have hnot : x ∉ connectedComponentIn (P ∪ D) (a i) := by
    rw [heq]
    rintro (hx' | hxD)
    · exact hxA hx'
    · exact hxA (hattach ⟨hx, hxD⟩)
  have hsub : connectedComponentIn (P ∪ D) x ⊆ P := by
    intro y hy
    rcases connectedComponentIn_subset _ _ hy with hyP | hyD
    · exact hyP
    · have hya := hDa hyD
      have hsame := (connectedComponentIn_eq hy).trans (connectedComponentIn_eq hya).symm
      exact False.elim (hnot (hsame ▸ mem_connectedComponentIn (Or.inl hx)))
  exact Subset.antisymm
    (isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn (Or.inl hx)) hsub)
    (connectedComponentIn_mono x subset_union_left)

end Topology
