import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Caps.Connected







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Nested
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false

open Set Metric Function

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

def capRegion (i : Fin 3) : Set S2 := ![southernCap, northernCap, upperCap] i

theorem capRegion_open (i : Fin 3) : IsOpen (capRegion i) := by
  fin_cases i
  · exact isOpen_southernCap
  · exact isOpen_northernCap
  · exact isOpen_upperCap

theorem capRegion_connected (i : Fin 3) : IsConnected (capRegion i) := by
  fin_cases i
  · exact isConnected_southernCap
  · exact isConnected_northernCap
  · exact isConnected_upperCap

theorem capRegion_disjoint : Pairwise (fun i j => Disjoint (capRegion i) (capRegion j)) := by
  have hSN : Disjoint southernCap northernCap := disjoint_left.mpr (fun p hp hq => by
    have := hp.2
    have := hq.2
    linarith)
  have hSU : Disjoint southernCap upperCap := disjoint_left.mpr (fun p hp hq => by
    have := hp.1
    change 13 / 10 < height p at hq
    linarith)
  have hNU : Disjoint northernCap upperCap := disjoint_left.mpr (fun p hp hq => by
    have := hp.1
    change 13 / 10 < height p at hq
    linarith)
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact hSN
  · exact hSU
  · exact hSN.symm
  · exact (hij rfl).elim
  · exact hNU
  · exact hSU.symm
  · exact hNU.symm
  · exact (hij rfl).elim

theorem capRegion_cover : (⋃ i, capRegion i) = retainedBandᶜ := by
  rw [retainedBand_compl]
  ext p
  simp only [mem_iUnion, mem_union]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
  · rintro ((h | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩

theorem connectedComponentIn_compl_retainedBand {i : Fin 3} {p : S2}
    (hp : p ∈ capRegion i) : connectedComponentIn retainedBandᶜ p=capRegion i := by
  let R : Set S2 := ⋃ j : {j : Fin 3 // j ≠ i}, capRegion j
  have hR : IsOpen R := isOpen_iUnion (fun j => capRegion_open j)
  have hsep : Disjoint (capRegion i) R := by
    apply disjoint_left.mpr
    intro x hxi hxR
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxR
    exact disjoint_left.mp (capRegion_disjoint j.property.symm) hxi hj
  have hsub : capRegion i ⊆ retainedBandᶜ :=
    fun x hx => capRegion_cover.subset (mem_iUnion_of_mem i hx)
  have hcover : retainedBandᶜ ⊆ capRegion i ∪ R := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (capRegion_cover.superset hx)
    by_cases hji : j=i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion_of_mem ⟨j, hji⟩ hj)
  apply Subset.antisymm
  · exact IsPreconnected.subset_left_of_subset_union (capRegion_open i) hR hsep
      ((connectedComponentIn_subset _ _).trans hcover)
      ⟨p, mem_connectedComponentIn (hsub hp), hp⟩ isPreconnected_connectedComponentIn
  · exact (capRegion_connected i).2.subset_connectedComponentIn hp hsub

theorem card_connectedComponents_compl_retainedBand :
    Nat.card (ConnectedComponents ↥retainedBandᶜ) = 3 := by
  classical
  choose p hp using fun i => (capRegion_connected i).nonempty
  have hsub (i : Fin 3) : capRegion i ⊆ retainedBandᶜ :=
    fun x hx => capRegion_cover.subset (mem_iUnion_of_mem i hx)
  let q (i : Fin 3) : ↥retainedBandᶜ := ⟨p i, hsub i (hp i)⟩
  let f (i : Fin 3) : ConnectedComponents ↥retainedBandᶜ := ConnectedComponents.mk (q i)
  have hcomponent (i : Fin 3) : connectedComponentIn retainedBandᶜ (p i)=capRegion i :=
    connectedComponentIn_compl_retainedBand (hp i)
  have hinj : Injective f := by
    intro i j hij
    have hm := (Poincare.Topology.connectedComponents_eq_iff_mem (q i) (q j)).mp hij
    change p i ∈ connectedComponentIn retainedBandᶜ (p j) at hm
    rw [hcomponent j] at hm
    by_contra hne
    exact disjoint_left.mp (capRegion_disjoint hne) (hp i) hm
  have hsurj : Surjective f := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨i, hi⟩ := mem_iUnion.mp (capRegion_cover.superset x.property)
    refine ⟨i, ?_⟩
    apply Eq.symm
    apply (Poincare.Topology.connectedComponents_eq_iff_mem x (q i)).mpr
    change (x : S2) ∈ connectedComponentIn retainedBandᶜ (p i)
    rw [hcomponent i]
    exact hi
  simpa using (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

end Poincare.Manifold.Schoenflies.Saddle.Nested

end

end M38Schoenflies
