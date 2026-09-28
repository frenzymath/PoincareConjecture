import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.ThreePortComponentCarriers
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.KneserConnectivityCases
import PoincareConjecture.Proofs.M76.Wall.PLDomainComponents

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_finite_port_component_domains
    {X ι J : Type*} [TopologicalSpace X] [T2Space X] [Finite J] [Nonempty J]
    {e : ι → OpenPartialHomeomorph X V3} {Q D : Set X}
    (hQ : IsCompact Q) (hPL : PLDomain e Q) (hD : IsClosed D)
    (hDc : IsConnected D) (hwhole : IsConnected (Q ∪ D))
    (p : J → Set X) (hp : ∀ i, IsConnected (p i))
    (hports : Q ∩ D = ⋃ i, p i) :
    ∃ (a : J → X) (C : J → Set X),
      (∀ i, a i ∈ p i ∧ a i ∈ Q ∧ C i = _root_.connectedComponentIn Q (a i)) ∧
      (∀ i, IsCompact (C i) ∧ PLDomain e (C i) ∧ IsConnected (C i) ∧
        C i ⊆ Q ∧ p i ⊆ C i) ∧
      Q = ⋃ i, C i ∧
      (∀ i j, C i = C j ∨ Disjoint (C i) (C j)) ∧
      (∀ i, frontier (C i) = C i ∩ frontier Q) ∧
      (∀ i, C i ∩ D = ⋃ j ∈ {j | C j = C i}, p j) ∧
      (∀ x ∈ Q, ∃ i, _root_.connectedComponentIn Q x = C i) := by
  classical
  let : LocallyPathConnectedSpace Q := hPL.locallyPathConnectedSpace
  choose a ha using fun i => (hp i).nonempty
  have hpQ (i : J) : p i ⊆ Q :=
    (subset_iUnion p i).trans (hports.symm.subset.trans inter_subset_left)
  have haQ (i : J) : a i ∈ Q := hpQ i (ha i)
  let C := fun i => _root_.connectedComponentIn Q (a i)
  have hsub (i : J) : C i ⊆ Q := connectedComponentIn_subset _ _
  have hcap (i : J) : p i ⊆ C i :=
    (hp i).isPreconnected.subset_connectedComponentIn (ha i) (hpQ i)
  have hcompact (i : J) : IsCompact (C i) :=
    isCompact_connectedComponentIn_of_mem hQ (haQ i)
  obtain ⟨i⟩ := ‹Nonempty J›
  have hmerged := (Topology.componentIn_closed_finite_port_attachment
    hQ.isClosed hD hDc p hp hports a ha i).1
  have hfull : _root_.connectedComponentIn (Q ∪ D) (a i) = Q ∪ D :=
    hwhole.isPreconnected.connectedComponentIn (Or.inl (haQ i))
  have hcover : Q = ⋃ j, C j := by
    apply Subset.antisymm
    · intro x hx
      have hxall : x ∈ (⋃ j, C j) ∪ D :=
        hmerged.subset (hfull.symm.subset (Or.inl hx))
      rcases hxall with hxC | hxD
      · exact hxC
      · obtain ⟨j, hxj⟩ := mem_iUnion.mp (hports.subset ⟨hx, hxD⟩)
        exact mem_iUnion.mpr ⟨j, hcap j hxj⟩
    · exact iUnion_subset hsub
  have hsame {j k : J} {x : X} (hxj : x ∈ C j) (hxk : x ∈ C k) : C j = C k :=
    (connectedComponentIn_eq hxj).trans (connectedComponentIn_eq hxk).symm
  refine ⟨a, C, (fun j => ⟨ha j, haQ j, rfl⟩), ?_, hcover, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨hcompact j, hPL.connectedComponentIn hQ (haQ j),
      isConnected_connectedComponentIn_iff.mpr (haQ j), hsub j, hcap j⟩
  · intro j k
    by_cases heq : C j = C k
    · exact Or.inl heq
    · exact Or.inr (disjoint_left.mpr fun _ hxj hxk => heq (hsame hxj hxk))
  · intro j
    obtain ⟨U, hU, hCU⟩ := exists_open_inter_of_relative_open (hsub j)
      (isOpen_preimage_connectedComponentIn (haQ j))
    exact frontier_eq_inter_of_eq_inter_open hQ.isClosed (hcompact j).isClosed hU hCU
  · intro j
    apply Subset.antisymm
    · rintro x ⟨hxC, hxD⟩
      obtain ⟨k, hxk⟩ := mem_iUnion.mp (hports.subset ⟨hsub j hxC, hxD⟩)
      exact mem_iUnion₂.mpr ⟨k, hsame (hcap k hxk) hxC, hxk⟩
    · intro x hx
      obtain ⟨k, heq, hxk⟩ := mem_iUnion₂.mp hx
      exact ⟨heq ▸ hcap k hxk, (hports.symm.subset (mem_iUnion.mpr ⟨k, hxk⟩)).2⟩
  · intro x hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp (hcover.subset hx)
    exact ⟨j, (connectedComponentIn_eq hxj).symm⟩

theorem PLDomain.exists_three_port_component_domains
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q D : Set X}
    (hQ : IsCompact Q) (hPL : PLDomain e Q) (hD : IsClosed D)
    (hDc : IsConnected D) (hwhole : IsConnected (Q ∪ D))
    (p : Fin 3 → Set X) (hp : ∀ i, IsConnected (p i))
    (hports : Q ∩ D = ⋃ i, p i) :
    ∃ (a : Fin 3 → X) (C : Fin 3 → Set X),
      (∀ i, a i ∈ p i ∧ a i ∈ Q ∧ C i = _root_.connectedComponentIn Q (a i)) ∧
      (∀ i, IsCompact (C i) ∧ PLDomain e (C i) ∧ IsConnected (C i) ∧
        C i ⊆ Q ∧ p i ⊆ C i) ∧
      Q = ⋃ i, C i ∧
      (∀ i j, C i = C j ∨ Disjoint (C i) (C j)) ∧
      (∀ i, frontier (C i) = C i ∩ frontier Q) ∧
      (∀ i, C i ∩ D = ⋃ j ∈ {j | C j = C i}, p j) ∧
      (∀ x ∈ Q, ∃ i, _root_.connectedComponentIn Q x = C i) ∧
      ((∀ i j, C i = C j) ∨
        (C 0 = C 1 ∧ C 0 ≠ C 2 ∧ C 1 ≠ C 2) ∨
        (C 0 = C 2 ∧ C 0 ≠ C 1 ∧ C 1 ≠ C 2) ∨
        (C 1 = C 2 ∧ C 0 ≠ C 1 ∧ C 0 ≠ C 2) ∨
        (C 0 ≠ C 1 ∧ C 0 ≠ C 2 ∧ C 1 ≠ C 2)) := by
  obtain ⟨a, C, ha, hC, hcover, hdis, hfront, hattach, hexhaust⟩ :=
    hPL.exists_finite_port_component_domains hQ hD hDc hwhole p hp hports
  refine ⟨a, C, ha, hC, hcover, hdis, hfront, hattach, hexhaust, ?_⟩
  exact fin3_equivalence_partition_cases (fun i j => C i = C j)
    (fun _ => rfl) (fun {_ _} h => h.symm) (fun {_ _ _} h h' => h.trans h')

end PoincareConjecture.M76
