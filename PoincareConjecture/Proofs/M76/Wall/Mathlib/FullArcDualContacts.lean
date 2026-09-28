import PoincareConjecture.Proofs.M76.Wall.Mathlib.FullArcEdgeFaces
import PoincareConjecture.Proofs.M76.Wall.Mathlib.DualStrictCoface

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

theorem full_arc_dual_contacts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K A : SimplicialComplex ℝ E) [Fintype K.faces] (hAK : A ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ A.vertices) → s ∈ A.faces)
    {n : ℕ} (p : Fin (n + 2) → E) (hinj : Function.Injective p)
    (hverts : ∀ i, p i ∈ A.vertices)
    (hedge : ∀ i : Fin (n + 1), {p i.castSucc, p i.succ} ∈ A.faces)
    (hcover : A.space = ⋃ i : Fin (n + 1), segment ℝ (p i.castSucc) (p i.succ)) :
    (∀ i : Fin (n + 1),
      (K.barycentricDualBlock {p i.castSucc}).space ∩
          (K.barycentricDualBlock {p i.succ}).space =
        (K.barycentricDualBlock {p i.castSucc, p i.succ}).space) ∧
      (∀ i : Fin (n + 1),
        (K.barycentricDualBlock {p i.castSucc, p i.succ}).space ⊆
            ((K.barycentricDualBlock {p i.castSucc}).link (p i.castSucc)).space ∧
          (K.barycentricDualBlock {p i.castSucc, p i.succ}).space ⊆
            ((K.barycentricDualBlock {p i.succ}).link (p i.succ)).space) ∧
      (∀ i j : Fin (n + 2), i.val + 1 < j.val →
        Disjoint (K.barycentricDualBlock {p i}).space (K.barycentricDualBlock {p j}).space) ∧
      ∀ i j : Fin (n + 1), i ≠ j →
        Disjoint (K.barycentricDualBlock {p i.castSucc, p i.succ}).space
          (K.barycentricDualBlock {p j.castSucc, p j.succ}).space := by
  have hfar (i j : Fin (n + 2)) (hij : i.val + 1 < j.val) :
      Disjoint (K.barycentricDualBlock {p i}).space (K.barycentricDualBlock {p j}).space := by
    have hne : i ≠ j := by intro h; have hv := congrArg Fin.val h; omega
    have hnot : {p i, p j} ∉ K.faces := by
      intro hs
      have h := (K.pair_mem_faces_iff_of_full_edge_chain A hAK hfull p hinj
        hverts hedge hcover hne).mp hs
      omega
    rw [disjoint_iff_inter_eq_empty, K.barycentricDualBlock_space_inter,
      Finset.singleton_union]
    exact K.barycentricDualBlock_space_eq_empty_of_not_face
      (Finset.insert_nonempty _ _) hnot
  have hstrict (a b : E) (hne : a ≠ b) : ({a} : Finset E) ⊂ {a, b} := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _), ?_⟩
    intro heq
    have hb : b ∈ ({a} : Finset E) := by rw [heq]; simp
    exact hne (Finset.mem_singleton.mp hb).symm
  have hleft (i : Fin (n + 1)) :
      (K.barycentricDualBlock {p i.castSucc, p i.succ}).space ⊆
        (K.barycentricDualBlock {p i.castSucc}).space :=
    space_subset_of_le (K.barycentricDualBlock_antitone
      (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)))
  have hright (i : Fin (n + 1)) :
      (K.barycentricDualBlock {p i.castSucc, p i.succ}).space ⊆
        (K.barycentricDualBlock {p i.succ}).space :=
    space_subset_of_le (K.barycentricDualBlock_antitone
      (Finset.singleton_subset_iff.mpr
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
  refine ⟨?_, ?_, hfar, ?_⟩
  · intro i
    rw [K.barycentricDualBlock_space_inter, Finset.singleton_union]
  · intro i
    have hne : p i.castSucc ≠ p i.succ := by
      intro h
      have heq := congrArg Fin.val (hinj h)
      change i.val = i.val + 1 at heq
      omega
    constructor
    · simpa only [Finset.centroid_singleton, id_eq] using
        space_subset_of_le (K.barycentricDualBlock_le_link_of_ssubset
          (hAK (hverts i.castSucc)) (hstrict _ _ hne))
    · simpa only [Finset.pair_comm (p i.succ) (p i.castSucc),
        Finset.centroid_singleton, id_eq] using
        space_subset_of_le (K.barycentricDualBlock_le_link_of_ssubset
          (hAK (hverts i.succ)) (hstrict _ _ hne.symm))
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hsep : i.castSucc.val + 1 < j.succ.val := by
        change i.val + 1 < j.val + 1
        exact Nat.add_lt_add_right hij 1
      exact (hfar i.castSucc j.succ hsep).mono (hleft i) (hright j)
    · have hsep : j.castSucc.val + 1 < i.succ.val := by
        change j.val + 1 < i.val + 1
        exact Nat.add_lt_add_right hji 1
      exact ((hfar j.castSucc i.succ hsep).mono (hleft j) (hright i)).symm

end Geometry.SimplicialComplex
