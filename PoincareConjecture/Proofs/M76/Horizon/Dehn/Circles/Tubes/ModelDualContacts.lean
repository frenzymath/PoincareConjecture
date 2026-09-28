import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.CyclicModelOrder
import PoincareConjecture.Proofs.M76.Wall.Mathlib.DualStrictCoface









set_option autoImplicit false
open Set Geometry

namespace Geometry.SimplicialComplex

private theorem cyclic_rotate_values {n : ℕ} (i : Fin (n + 3)) :
    (finRotate (n + 3) i).val = i.val + 1 ∨
      (i.val = n + 2 ∧ (finRotate (n + 3) i).val = 0) := by
  rw [coe_finRotate]
  split_ifs with h
  · right
    subst i
    exact ⟨rfl, rfl⟩
  · exact Or.inl rfl

private theorem cyclic_rotate_ne {n : ℕ} (i : Fin (n + 3)) :
    i ≠ finRotate (n + 3) i := by
  intro h
  have hv := congrArg Fin.val h
  have := cyclic_rotate_values i
  omega

private theorem cyclic_edge_subset_index
    {E : Type*} [DecidableEq E] {n : ℕ} (p : Fin (n + 3) → E)
    (hinj : Function.Injective p) {i j : Fin (n + 3)}
    (h : ({p i, p (finRotate (n + 3) i)} : Finset E) ⊆
      {p j, p (finRotate (n + 3) j)}) : i = j := by
  have h0 := h (Finset.mem_insert_self _ _)
  have h1 := h (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  simp only [Finset.mem_insert, Finset.mem_singleton, hinj.eq_iff] at h0 h1
  rcases h0 with h0 | h0
  · exact h0
  rcases h1 with h1 | h1
  · have h0v := congrArg Fin.val h0
    have h1v := congrArg Fin.val h1
    have := cyclic_rotate_values i
    have := cyclic_rotate_values j
    omega
  · exact False.elim ((cyclic_rotate_ne i) (h0.trans h1.symm))



theorem full_cyclic_dual_contacts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K A : SimplicialComplex ℝ E) [Fintype K.faces] (hAK : A ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ A.vertices) → s ∈ A.faces)
    {n : ℕ} (p : Fin (n + 3) → E) (hinj : Function.Injective p)
    (hverts : range p = A.vertices)
    (hfaces : ∀ s : Finset E, s ∈ A.faces ↔ s.Nonempty ∧
      ∃ j : Fin (n + 3), s ⊆ {p j, p (finRotate (n + 3) j)}) :
    (∀ i, (K.barycentricDualBlock {p i}).space ∩
        (K.barycentricDualBlock {p (finRotate (n + 3) i)}).space =
      (K.barycentricDualBlock {p i, p (finRotate (n + 3) i)}).space) ∧
    (∀ i, (K.barycentricDualBlock {p i, p (finRotate (n + 3) i)}).space ⊆
        ((K.barycentricDualBlock {p i}).link (p i)).space ∧
      (K.barycentricDualBlock {p i, p (finRotate (n + 3) i)}).space ⊆
        ((K.barycentricDualBlock {p (finRotate (n + 3) i)}).link
          (p (finRotate (n + 3) i))).space) ∧
    (∀ i j, i ≠ j → j ≠ finRotate (n + 3) i → i ≠ finRotate (n + 3) j →
      Disjoint (K.barycentricDualBlock {p i}).space
        (K.barycentricDualBlock {p j}).space) ∧
    (∀ i j, i ≠ j →
      Disjoint (K.barycentricDualBlock {p i, p (finRotate (n + 3) i)}).space
        (K.barycentricDualBlock {p j, p (finRotate (n + 3) j)}).space) ∧
    (⋃ i, (K.barycentricDualBlock {p i}).space) =
      (K.barycentricNeighborhood A).space := by
  have hv (i) : p i ∈ A.vertices := hverts ▸ mem_range_self i
  have hstrict (a b : E) (hne : a ≠ b) : ({a} : Finset E) ⊂ {a, b} := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨by simp, ?_⟩
    intro heq
    have hb : b ∈ ({a} : Finset E) := by rw [heq]; simp
    exact hne (Finset.mem_singleton.mp hb).symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [K.barycentricDualBlock_space_inter, Finset.singleton_union]
  · intro i
    have hne := hinj.ne (cyclic_rotate_ne i)
    constructor
    · simpa only [Finset.centroid_singleton, id_eq] using
        space_subset_of_le (K.barycentricDualBlock_le_link_of_ssubset
          (hAK (hv i)) (hstrict _ _ hne))
    · simpa only [Finset.pair_comm (p (finRotate (n + 3) i)) (p i),
        Finset.centroid_singleton, id_eq] using
        space_subset_of_le (K.barycentricDualBlock_le_link_of_ssubset
          (hAK (hv (finRotate (n + 3) i))) (hstrict _ _ hne.symm))
  · intro i j hij hji hij'
    have hnot : {p i, p j} ∉ K.faces := by
      intro hs
      have hsA := hfull _ hs (by
        intro v hv'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv'
        rcases hv' with rfl | rfl <;> exact hv _)
      obtain ⟨k, hk⟩ := ((hfaces _).mp hsA).2
      have hi := hk (Finset.mem_insert_self _ _)
      have hj := hk (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      simp only [Finset.mem_insert, Finset.mem_singleton, hinj.eq_iff] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact hij rfl
      · exact hji rfl
      · exact hij' rfl
      · exact hij rfl
    rw [disjoint_iff_inter_eq_empty, K.barycentricDualBlock_space_inter,
      Finset.singleton_union]
    exact K.barycentricDualBlock_space_eq_empty_of_not_face
      (Finset.insert_nonempty _ _) hnot
  · intro i j hij
    have hnot : ({p i, p (finRotate (n + 3) i)} ∪
        {p j, p (finRotate (n + 3) j)} : Finset E) ∉ K.faces := by
      intro hs
      have hsA := hfull _ hs (by
        intro v hv'
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hv'
        rcases hv' with (rfl | rfl) | (rfl | rfl) <;> exact hv _)
      obtain ⟨k, hk⟩ := ((hfaces _).mp hsA).2
      have hik := cyclic_edge_subset_index p hinj (Finset.Subset.trans
        Finset.subset_union_left hk)
      have hjk := cyclic_edge_subset_index p hinj (Finset.Subset.trans
        Finset.subset_union_right hk)
      exact hij (hik.trans hjk.symm)
    rw [disjoint_iff_inter_eq_empty, K.barycentricDualBlock_space_inter]
    exact K.barycentricDualBlock_space_eq_empty_of_not_face
      (Finset.union_nonempty.mpr (Or.inl (Finset.insert_nonempty _ _))) hnot
  · rw [K.barycentricNeighborhood_space_eq_iUnion_dualBlocks, ← hverts]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨p i, mem_range_self i, hxi⟩
    · intro hx
      obtain ⟨v, ⟨i, rfl⟩, hxi⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion.mpr ⟨i, hxi⟩



theorem full_cyclic_dual_contacts_linear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K A : SimplicialComplex ℝ E) [Fintype K.faces] (hAK : A ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ A.vertices) → s ∈ A.faces)
    {n : ℕ} (p : Fin (n + 3) → E) (hinj : Function.Injective p)
    (hverts : range p = A.vertices)
    (hfaces : ∀ s : Finset E, s ∈ A.faces ↔ s.Nonempty ∧
      ∃ j : Fin (n + 3), s ⊆ {p j, p (finRotate (n + 3) j)}) :
    let B := fun i ↦ (K.barycentricDualBlock {p i}).space
    let J := fun i : Fin (n + 2) ↦
      (K.barycentricDualBlock {p i.castSucc, p i.succ}).space
    let Jclose := (K.barycentricDualBlock {p (Fin.last (n + 2)), p 0}).space
    (∀ i, B i.castSucc ∩ B i.succ = J i) ∧
    B 0 ∩ B (Fin.last (n + 2)) = Jclose ∧
    (∀ i, J i ⊆ ((K.barycentricDualBlock {p i.castSucc}).link (p i.castSucc)).space ∧
      J i ⊆ ((K.barycentricDualBlock {p i.succ}).link (p i.succ)).space) ∧
    (Jclose ⊆ ((K.barycentricDualBlock {p (Fin.last (n + 2))}).link
      (p (Fin.last (n + 2)))).space ∧
      Jclose ⊆ ((K.barycentricDualBlock {p 0}).link (p 0)).space) ∧
    (∀ i j, i.val + 1 < j.val → ¬ (i = 0 ∧ j = Fin.last (n + 2)) →
      Disjoint (B i) (B j)) ∧
    (∀ i j, i ≠ j → Disjoint (J i) (J j)) ∧
    (∀ i, Disjoint (J i) Jclose) ∧
    (⋃ i, B i) = (K.barycentricNeighborhood A).space := by
  obtain ⟨hcontact, hlink, hfar, hjoints, hcover⟩ :=
    K.full_cyclic_dual_contacts A hAK hfull p hinj hverts hfaces
  have hsucc (i : Fin (n + 2)) : finRotate (n + 3) i.castSucc = i.succ := by
    apply Fin.ext
    rw [coe_finRotate_of_ne_last]
    · rfl
    · intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at this
      omega
  have hclose : finRotate (n + 3) (Fin.last (n + 2)) = 0 := finRotate_last
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hcover⟩
  · intro i
    simpa only [hsucc] using hcontact i.castSucc
  · simpa only [hclose, inter_comm] using hcontact (Fin.last (n + 2))
  · intro i
    simpa only [hsucc] using hlink i.castSucc
  · simpa only [hclose] using hlink (Fin.last (n + 2))
  · intro i j hij hclosing
    apply hfar i j
    · intro h
      have := congrArg Fin.val h
      omega
    · intro h
      have hv := congrArg Fin.val h
      have := cyclic_rotate_values i
      omega
    · intro h
      have hv := congrArg Fin.val h
      rcases cyclic_rotate_values j with hs | ⟨hl, hz⟩
      · omega
      · apply hclosing
        exact ⟨Fin.ext (by simpa only [Fin.val_zero] using hv.trans hz), Fin.ext hl⟩
  · intro i j hij
    have hij' : i.castSucc ≠ j.castSucc := by
      intro h
      exact hij (Fin.castSucc_injective _ h)
    simpa only [hsucc] using hjoints i.castSucc j.castSucc hij'
  · intro i
    have hne : i.castSucc ≠ Fin.last (n + 2) := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at this
      omega
    simpa only [hsucc, hclose] using hjoints i.castSucc (Fin.last (n + 2)) hne

end Geometry.SimplicialComplex
