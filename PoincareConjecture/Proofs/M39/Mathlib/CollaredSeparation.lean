import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false

open Set

variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]

theorem IsOpen.frontier_connectedComponentIn_subset_compl {F : Set X}
    (hF : IsOpen F) (x : X) :
    frontier (connectedComponentIn F x) ⊆ Fᶜ := by
  intro y hy hyF
  rw [hF.connectedComponentIn.frontier_eq] at hy
  obtain ⟨z, hzY, hzX⟩ := mem_closure_iff.mp hy.1
    (connectedComponentIn F y) hF.connectedComponentIn (mem_connectedComponentIn hyF)
  have hEq : connectedComponentIn F x = connectedComponentIn F y :=
    (connectedComponentIn_eq hzX).trans (connectedComponentIn_eq hzY).symm
  apply hy.2
  rw [hEq]
  exact mem_connectedComponentIn hyF

theorem exists_separating_components_of_collar [ConnectedSpace X]
    {S U N P : Set X} (hS : IsClosed S) (hSne : S.Nonempty)
    (hU : IsOpen U) (hSU : S ⊆ U) (hcollar : U \ S = N ∪ P)
    (hN : IsConnected N) (hP : IsConnected P)
    (hSN : S ⊆ closure N) (hSP : S ⊆ closure P)
    (hsep : ¬ IsConnected Sᶜ) :
    ∃ V W : Set X, IsOpen V ∧ IsOpen W ∧ IsConnected V ∧ IsConnected W ∧
      P ⊆ V ∧ N ⊆ W ∧ Disjoint V W ∧ V ∪ W = Sᶜ ∧
      frontier V = S ∧ frontier W = S := by
  have hNF : N ⊆ Sᶜ := fun _ hx => (hcollar.symm.subset (Or.inl hx)).2
  have hPF : P ⊆ Sᶜ := fun _ hx => (hcollar.symm.subset (Or.inr hx)).2
  obtain ⟨n, hn⟩ := hN.nonempty
  obtain ⟨p, hp⟩ := hP.nonempty
  let Cn := connectedComponentIn Sᶜ n
  let Cp := connectedComponentIn Sᶜ p
  have hNC : N ⊆ Cn := hN.isPreconnected.subset_connectedComponentIn hn hNF
  have hPC : P ⊆ Cp := hP.isPreconnected.subset_connectedComponentIn hp hPF
  have hmeet : ∀ x ∈ Sᶜ, (U ∩ connectedComponentIn Sᶜ x).Nonempty := by
    intro x hx
    have hproper : connectedComponentIn Sᶜ x ≠ univ := by
      intro heq
      obtain ⟨s, hs⟩ := hSne
      have hsC : s ∈ connectedComponentIn Sᶜ x := heq.symm ▸ mem_univ s
      exact connectedComponentIn_subset Sᶜ x hsC hs
    obtain ⟨z, hz⟩ := nonempty_frontier_iff.mpr
      ⟨⟨x, mem_connectedComponentIn hx⟩, hproper⟩
    have hzS : z ∈ S := by
      simpa only [compl_compl] using
        hS.isOpen_compl.frontier_connectedComponentIn_subset_compl x hz
    exact mem_closure_iff.mp (frontier_subset_closure hz) U hU (hSU hzS)
  have hclassify : ∀ x ∈ Sᶜ,
      connectedComponentIn Sᶜ x = Cn ∨ connectedComponentIn Sᶜ x = Cp := by
    intro x hx
    obtain ⟨y, hyU, hyC⟩ := hmeet x hx
    have hyS := connectedComponentIn_subset Sᶜ x hyC
    have hyNP : y ∈ N ∪ P := hcollar.subset ⟨hyU, hyS⟩
    rcases hyNP with hyN | hyP
    · exact Or.inl ((connectedComponentIn_eq hyC).trans
        (connectedComponentIn_eq (hNC hyN)).symm)
    · exact Or.inr ((connectedComponentIn_eq hyC).trans
        (connectedComponentIn_eq (hPC hyP)).symm)
  have hne : Cn ≠ Cp := by
    intro heq
    apply hsep
    have hcover : Sᶜ = Cn := by
      apply subset_antisymm
      · intro x hx
        have hxC : connectedComponentIn Sᶜ x = Cn :=
          (hclassify x hx).elim id (fun h => h.trans heq.symm)
        rw [← hxC]
        exact mem_connectedComponentIn hx
      · exact connectedComponentIn_subset Sᶜ n
    rw [hcover]
    exact isConnected_connectedComponentIn_iff.mpr (hNF hn)
  have hdisjoint : Disjoint Cp Cn := by
    apply Set.disjoint_left.mpr
    intro x hxP hxN
    exact hne ((connectedComponentIn_eq hxN).trans (connectedComponentIn_eq hxP).symm)
  have hcover : Cp ∪ Cn = Sᶜ := by
    apply subset_antisymm
    · exact union_subset (connectedComponentIn_subset Sᶜ p)
        (connectedComponentIn_subset Sᶜ n)
    · intro x hx
      rcases hclassify x hx with hxn | hxp
      · exact Or.inr (hxn ▸ mem_connectedComponentIn hx)
      · exact Or.inl (hxp ▸ mem_connectedComponentIn hx)
  have hfrontier : ∀ (a : X) (H : Set X), H ⊆ connectedComponentIn Sᶜ a →
      S ⊆ closure H → frontier (connectedComponentIn Sᶜ a) = S := by
    intro a H hHC hSH
    apply subset_antisymm
    · simpa only [compl_compl] using
        hS.isOpen_compl.frontier_connectedComponentIn_subset_compl a
    · intro x hx
      rw [hS.isOpen_compl.connectedComponentIn.frontier_eq]
      exact ⟨closure_mono hHC (hSH hx), fun hxC =>
        connectedComponentIn_subset Sᶜ a hxC hx⟩
  exact ⟨Cp, Cn, hS.isOpen_compl.connectedComponentIn,
    hS.isOpen_compl.connectedComponentIn,
    isConnected_connectedComponentIn_iff.mpr (hPF hp),
    isConnected_connectedComponentIn_iff.mpr (hNF hn), hPC, hNC, hdisjoint,
    hcover, hfrontier p P hPC hSP, hfrontier n N hNC hSN⟩
