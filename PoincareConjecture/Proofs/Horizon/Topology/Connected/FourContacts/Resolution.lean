import PoincareConjecture.Proofs.Horizon.Topology.Connected.FiniteBoundaryComponents
import Mathlib.Tactic.FinCases

noncomputable section
set_option autoImplicit false

open Set Function

namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X]

theorem connectedComponentIn_eq_of_finite_closed_cover
    {I : Type*} [Finite I] (C : I → Set X)
    (hclosed : ∀ i, IsClosed (C i)) (hconn : ∀ i, IsPreconnected (C i))
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    {L : Set X} (hcover : (⋃ i, C i) = L) {i : I} {p : X} (hp : p ∈ C i) :
    connectedComponentIn L p = C i := by
  classical
  let R : Set X := ⋃ j : {j : I // j ≠ i}, C j
  have hR : IsClosed R := isClosed_iUnion_of_finite (fun j => hclosed j)
  have hsep : Disjoint (C i) R := by
    apply disjoint_left.mpr
    intro x hxi hxR
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxR
    exact disjoint_left.mp (hdisjoint j.property.symm) hxi hj
  have hsub : C i ⊆ L := fun x hx => hcover.subset (mem_iUnion_of_mem i hx)
  have hLR : L ⊆ C i ∪ R := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover.superset hx)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion_of_mem ⟨j, hji⟩ hj)
  apply Subset.antisymm
  · have hparts := isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_connectedComponentIn (x := p) (F := L))
      (C i) R (hclosed i) hR ((connectedComponentIn_subset L p).trans hLR)
      (by rw [hsep.inter_eq, inter_empty])
    rcases hparts with hleft | hright
    · exact hleft
    · exact False.elim (disjoint_left.mp hsep hp
        (hright (mem_connectedComponentIn (hsub hp))))
  · exact (hconn i).subset_connectedComponentIn hp hsub

theorem card_connectedComponents_of_finite_closed_cover
    {I : Type*} [Finite I] (C : I → Set X)
    (hclosed : ∀ i, IsClosed (C i)) (hconn : ∀ i, IsConnected (C i))
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    {L : Set X} (hcover : (⋃ i, C i) = L) :
    Nat.card (ConnectedComponents L) = Nat.card I := by
  classical
  choose p hp using fun i => (hconn i).nonempty
  have hsub (i : I) : C i ⊆ L := fun x hx => hcover.subset (mem_iUnion_of_mem i hx)
  let q (i : I) : L := ⟨p i, hsub i (hp i)⟩
  let f (i : I) : ConnectedComponents L := ConnectedComponents.mk (q i)
  have hcomponent (i : I) : connectedComponentIn L (p i) = C i :=
    connectedComponentIn_eq_of_finite_closed_cover C hclosed
      (fun j => (hconn j).isPreconnected) hdisjoint hcover (hp i)
  have hinj : Injective f := by
    intro i j hij
    have hm := (connectedComponents_eq_iff_mem (q i) (q j)).mp hij
    change p i ∈ connectedComponentIn L (p j) at hm
    rw [hcomponent j] at hm
    by_contra hne
    exact disjoint_left.mp (hdisjoint hne) (hp i) hm
  have hsurj : Surjective f := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.superset x.property)
    refine ⟨i, ?_⟩
    apply Eq.symm
    apply (connectedComponents_eq_iff_mem x (q i)).mpr
    change (x : X) ∈ connectedComponentIn L (p i)
    rw [hcomponent i]
    exact hi
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

theorem isConnected_four_arc_resolution_crossed
    (A B : Fin 2 → Set X) (b : Fin 2 × Fin 2 → X)
    (hA : ∀ i, IsConnected (A i)) (hB : ∀ i, IsConnected (B i))
    (hbA : ∀ i, b i ∈ A i.1) (hbB : ∀ i, b i ∈ B i.2) :
    IsConnected ((⋃ i, A i) ∪ ⋃ i, B i) := by
  have h00 : IsConnected (A 0 ∪ B 0) :=
    (hA 0).union ⟨b (0, 0), hbA (0, 0), hbB (0, 0)⟩ (hB 0)
  have h10 : IsConnected ((A 0 ∪ B 0) ∪ A 1) :=
    h00.union ⟨b (1, 0), Or.inr (hbB (1, 0)), hbA (1, 0)⟩ (hA 1)
  have h01 : IsConnected (((A 0 ∪ B 0) ∪ A 1) ∪ B 1) :=
    h10.union ⟨b (0, 1), Or.inl (Or.inl (hbA (0, 1))), hbB (0, 1)⟩ (hB 1)
  have heq : (((A 0 ∪ B 0) ∪ A 1) ∪ B 1) = (⋃ i, A i) ∪ ⋃ i, B i := by
    ext x
    simp only [mem_union, mem_iUnion, Fin.exists_fin_two]
    tauto
  exact heq ▸ h01

theorem card_connectedComponents_four_arc_resolution_crossed
    (A B : Fin 2 → Set X) (b : Fin 2 × Fin 2 → X)
    (hA : ∀ i, IsConnected (A i)) (hB : ∀ i, IsConnected (B i))
    (hbA : ∀ i, b i ∈ A i.1) (hbB : ∀ i, b i ∈ B i.2) :
    Nat.card (ConnectedComponents ↥((⋃ i, A i) ∪ ⋃ i, B i)) = 1 := by
  let : ConnectedSpace ↥((⋃ i, A i) ∪ ⋃ i, B i) :=
    isConnected_iff_connectedSpace.mp (isConnected_four_arc_resolution_crossed A B b hA hB hbA hbB)
  exact Nat.card_unique

theorem four_arc_resolution_parallel
    (A B : Fin 2 → Set X) (b : Fin 2 × Fin 2 → X)
    (hAc : ∀ i, IsClosed (A i)) (hBc : ∀ i, IsClosed (B i))
    (hA : ∀ i, IsConnected (A i)) (hB : ∀ i, IsConnected (B i))
    (hAd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hBd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hbA : ∀ i, b i ∈ A i.1) (hbB : ∀ i, b i ∈ B i.1)
    (hmeet : ∀ i j, A i ∩ B j ⊆ range b) :
    let L := (⋃ i, A i) ∪ ⋃ i, B i
    (∀ i p, p ∈ A i ∪ B i → connectedComponentIn L p = A i ∪ B i) ∧
      Pairwise (fun i j => Disjoint (A i ∪ B i) (A j ∪ B j)) ∧
      Nat.card (ConnectedComponents L) = 2 := by
  let C (i : Fin 2) := A i ∪ B i
  have hclosed (i : Fin 2) : IsClosed (C i) := (hAc i).union (hBc i)
  have hconn (i : Fin 2) : IsConnected (C i) :=
    (hA i).union ⟨b (i, 0), hbA (i, 0), hbB (i, 0)⟩ (hB i)
  have hcross (i j : Fin 2) (hij : i ≠ j) : Disjoint (A i) (B j) := by
    apply disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨k, rfl⟩ := hmeet i j ⟨hxi, hxj⟩
    have hki : k.1 = i := by
      by_contra hne
      exact disjoint_left.mp (hAd hne) (hbA k) hxi
    have hkj : k.1 = j := by
      by_contra hne
      exact disjoint_left.mp (hBd hne) (hbB k) hxj
    exact hij (hki.symm.trans hkj)
  have hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    exact disjoint_union_left.mpr ⟨
      disjoint_union_right.mpr ⟨hAd hij, hcross i j hij⟩,
      disjoint_union_right.mpr ⟨(hcross j i hij.symm).symm, hBd hij⟩⟩
  have hcover : (⋃ i, C i) = (⋃ i, A i) ∪ ⋃ i, B i := iUnion_union_distrib A B
  dsimp only
  refine ⟨fun i p hp => connectedComponentIn_eq_of_finite_closed_cover C hclosed
    (fun i => (hconn i).isPreconnected) hdisjoint hcover hp, hdisjoint, ?_⟩
  simpa using card_connectedComponents_of_finite_closed_cover C hclosed hconn hdisjoint hcover

theorem contact_index_eq_iff_mem_connectedComponentIn
    {I J : Type*} [Finite I] (C : I → Set X)
    (hclosed : ∀ i, IsClosed (C i)) (hconn : ∀ i, IsPreconnected (C i))
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    {L : Set X} (hcover : (⋃ i, C i) = L)
    (b : J → X) (k : J → I) (hb : ∀ j, b j ∈ C (k j)) (i j : J) :
    k i = k j ↔ b i ∈ connectedComponentIn L (b j) := by
  rw [connectedComponentIn_eq_of_finite_closed_cover C hclosed hconn hdisjoint hcover (hb j)]
  constructor
  · intro he
    exact he ▸ hb i
  · intro hi
    by_contra hne
    exact disjoint_left.mp (hdisjoint hne) (hb i) hi

theorem exists_equiv_of_four_contact_first_pairing
    (k : Fin 2 × Fin 2 → Fin 2)
    (hk : ∀ i j, k i = k j ↔ i.1 = j.1) :
    ∃ E : Fin 2 ≃ Fin 2, ∀ i, k i = E i.1 := by
  let f (i : Fin 2) := k (i, 0)
  have hinj : Injective f := fun i j hij => (hk (i, 0) (j, 0)).mp hij
  let E : Fin 2 ≃ Fin 2 := Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  exact ⟨E, fun i => (hk i (i.1, 0)).mpr rfl⟩

theorem exists_equiv_of_four_contact_second_pairing
    (k : Fin 2 × Fin 2 → Fin 2)
    (hk : ∀ i j, k i = k j ↔ i.2 = j.2) :
    ∃ E : Fin 2 ≃ Fin 2, ∀ i, k i = E i.2 := by
  let f (i : Fin 2) := k (0, i)
  have hinj : Injective f := fun i j hij => (hk (0, i) (0, j)).mp hij
  let E : Fin 2 ≃ Fin 2 := Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  exact ⟨E, fun i => (hk i (0, i.2)).mpr rfl⟩

end Poincare.Topology
