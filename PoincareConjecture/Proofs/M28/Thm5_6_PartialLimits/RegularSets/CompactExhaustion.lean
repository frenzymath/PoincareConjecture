import PoincareConjecture.Proofs.M07.Topology.Exhaustion










set_option autoImplicit false

open Set

namespace PoincareConjecture.M28




theorem exists_connected_open_exhaustion_capturing_compacts
    {X : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
    [LocallyConnectedSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
    (p : X) (K : ℕ → Set X) (hK : ∀ j, IsCompact (K j)) :
    ∃ E : ℕ → Set X,
      (∀ j, IsOpen (E j)) ∧ (∀ j, IsConnected (E j)) ∧
      (∀ j, p ∈ E j) ∧ (∀ j, IsCompact (closure (E j))) ∧
      (∀ j, closure (E j) ⊆ E (j + 1)) ∧
      (⋃ j, E j) = univ ∧ ∀ j, K j ⊆ E j := by
  classical
  obtain ⟨V, hV, hVc, hVK, hVstep, hVcover, hpV⟩ :=
    Poincare.exists_connected_open_exhaustion p
  have hVmono : Monotone V := monotone_nat_of_le_succ hVstep
  have hcapture (A : Set X) (hA : IsCompact A) : ∃ j, A ⊆ V j :=
    hA.elim_directed_cover V hV (by rw [hVcover]; exact subset_univ _)
      hVmono.directed_le
  obtain ⟨b, hb⟩ := hcapture (K 0) (hK 0)
  have hnext (j m : ℕ) : ∃ l, j + 1 ≤ l ∧
      closure (V m) ∪ K (j + 1) ⊆ V l := by
    obtain ⟨l, hl⟩ := hcapture (closure (V m) ∪ K (j + 1))
      ((hVK m).union (hK (j + 1)))
    refine ⟨max l (j + 1), le_max_right _ _, ?_⟩
    exact hl.trans (hVmono (le_max_left _ _))
  choose next hnextJ hnextSub using hnext
  let a : ℕ → ℕ := fun j => Nat.rec b (fun j m => next j m) j
  have ha (j : ℕ) : j ≤ a j := by
    cases j with
    | zero => exact Nat.zero_le _
    | succ j => exact hnextJ j (a j)
  refine ⟨fun j => V (a j), fun j => hV (a j), fun j => hVc (a j),
    fun j => hpV (a j), fun j => hVK (a j), ?_, ?_, ?_⟩
  · intro j
    exact subset_union_left.trans (hnextSub j (a j))
  · apply iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨j, hj⟩ := iUnion_eq_univ_iff.mp hVcover x
    exact ⟨j, hVmono (ha j) hj⟩
  · intro j
    cases j with
    | zero => exact hb
    | succ j => exact subset_union_right.trans (hnextSub j (a j))

end PoincareConjecture.M28
