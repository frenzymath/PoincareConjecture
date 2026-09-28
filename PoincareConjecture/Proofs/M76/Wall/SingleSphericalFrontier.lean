import PoincareConjecture.Proofs.M76.Wall.FiniteSphereFamilyReduction











set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)






theorem exists_single_spherical_frontier_of_filled_family
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R P : Set X}
    (hR : PLDomain e R) (hRconn : IsConnected R) (hend : HasOneSimplyConnectedEnd R)
    (hP : IsClosed P) (hPR : P ⊆ R) (hBP : frontier R ⊆ P) :
    ∀ n : ℕ, 0 < n → ∀ L : Set X,
      PLDomain e L → IsCompact L → IsConnected L → L ⊆ R →
      (Subtype.val : R → X) ⁻¹' P ⊆ interior ((Subtype.val : R → X) ⁻¹' L) →
      IsConnected (((Subtype.val : R → X) ⁻¹' L)ᶜ) →
      ∀ S : Fin n → Set X,
      (∀ i, Nonempty (ChartwisePLSphere e (S i))) →
      (Pairwise fun i j => Disjoint (S i) (S j)) →
      (∀ i, S i ⊆ interior R) →
      frontier L = frontier R ∪ (⋃ i, S i) →
      frontier ((Subtype.val : R → X) ⁻¹' L) =
        (Subtype.val : R → X) ⁻¹' (⋃ i, S i) →
      ∃ M T : Set X, IsCompact M ∧ IsConnected M ∧ L ⊆ M ∧ M ⊆ R ∧
        PLDomain e M ∧ Nonempty (ChartwisePLSphere e T) ∧ T ⊆ interior R ∧
        Disjoint (frontier R) T ∧ frontier M = frontier R ∪ T ∧
        frontier ((Subtype.val : R → X) ⁻¹' M) = (Subtype.val : R → X) ⁻¹' T ∧
        (Subtype.val : R → X) ⁻¹' P ⊆ interior ((Subtype.val : R → X) ⁻¹' M) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn L hL hLc hLconn hLR hprotect hcompl S hS hdisjoint hSint hfront hrel
    by_cases hn1 : n = 1
    · subst n
      have hunion : (⋃ i : Fin 1, S i) = S 0 := by
        apply Subset.antisymm
        · intro x hx
          obtain ⟨i, hi⟩ := mem_iUnion.mp hx
          have hi0 : i = 0 := Subsingleton.elim _ _
          simpa only [hi0] using hi
        · exact fun _ hx => mem_iUnion.mpr ⟨0, hx⟩
      refine ⟨L, S 0, hLc, hLconn, subset_rfl, hLR, hL, hS 0, hSint 0, ?_, ?_, ?_, hprotect⟩
      · exact disjoint_left.mpr fun _ hxB hxS => hxB.2 (hSint 0 hxS)
      · simpa only [hunion] using hfront
      · simpa only [hunion] using hrel
    · have hn2 : 2 ≤ n := by omega
      let a : Fin n := ⟨0, by omega⟩
      let b : Fin n := ⟨1, by omega⟩
      have hab : a ≠ b := by
        intro h
        have hv := congrArg Fin.val h
        change (0 : ℕ) = 1 at hv
        omega
      obtain ⟨Lnew, m, Snew, hm, hsmaller, hLc', hLconn', hLLnew, hLnewR,
        hLnew, hSnew, hdisjointNew, hSintNew, hfrontNew, hrelNew, hcomplNew, hprotectNew⟩ :=
        exists_smaller_filled_spherical_family hR hRconn hend hL hLc hLconn hLR
          hP hPR hBP hprotect hcompl S hS hdisjoint hSint hfront a b hab
      have hmn : m < n := by simpa only [Nat.card_fin] using hsmaller
      obtain ⟨M, T, hMc, hMconn, hLnewM, hMR, hM, hT, hTint, hBT, hfrontM, hrelM, hprotectM⟩ :=
        ih m hmn hm Lnew hLnew hLc' hLconn' hLnewR hprotectNew hcomplNew
          Snew hSnew hdisjointNew hSintNew hfrontNew hrelNew
      exact ⟨M, T, hMc, hMconn, hLLnew.trans hLnewM, hMR, hM, hT, hTint,
        hBT, hfrontM, hrelM, hprotectM⟩






theorem exists_single_spherical_frontier_of_finite_family
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R K P : Set X}
    (hR : PLDomain e R) (hRconn : IsConnected R) (hend : HasOneSimplyConnectedEnd R)
    (hK : PLDomain e K) (hKc : IsCompact K) (hKconn : IsConnected K) (hKR : K ⊆ R)
    (hP : IsClosed P) (hPR : P ⊆ R) (hBP : frontier R ⊆ P)
    (hprotect : (Subtype.val : R → X) ⁻¹' P ⊆
      interior ((Subtype.val : R → X) ⁻¹' K))
    (S : κ → Set X) (hS : ∀ i, Nonempty (ChartwisePLSphere e (S i)))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (hSint : ∀ i, S i ⊆ interior R)
    (hfront : frontier K = frontier R ∪ ⋃ i, S i) :
    ∃ M T : Set X, IsCompact M ∧ IsConnected M ∧ K ⊆ M ∧ M ⊆ R ∧
      PLDomain e M ∧ Nonempty (ChartwisePLSphere e T) ∧ T ⊆ interior R ∧
      Disjoint (frontier R) T ∧ frontier M = frontier R ∪ T ∧
      frontier ((Subtype.val : R → X) ⁻¹' M) = (Subtype.val : R → X) ⁻¹' T ∧
      (Subtype.val : R → X) ⁻¹' P ⊆ interior ((Subtype.val : R → X) ⁻¹' M) := by
  have hrel : frontier ((Subtype.val : R → X) ⁻¹' K) =
      (Subtype.val : R → X) ⁻¹' (⋃ i, S i) :=
    protected_relative_frontier_eq_of_frontier hR.closed hK.closed hKR
      (iUnion_subset hSint) (fun _ hx => hprotect (hBP hx)) hfront
  obtain ⟨L, n, pick, hn, _, hLc, hLconn, hKL, hLR, hL, hfrontL, hrelL, hcompl, hprot⟩ :=
    exists_indexed_spherical_frontier_filling hR hRconn hend hK hKc hKconn hKR
      S hS hdisjoint hSint hfront hrel hBP hprotect
  obtain ⟨M, T, hMc, hMconn, hLM, hMR, hM, hT, hTint, hBT, hfrontM, hrelM, hprotectM⟩ :=
    exists_single_spherical_frontier_of_filled_family hR hRconn hend hP hPR hBP
      n hn L hL hLc hLconn hLR hprot hcompl (fun i => S (pick i))
      (fun i => hS (pick i)) (fun _ _ hij => hdisjoint (fun h => hij (pick.injective h)))
      (fun i => hSint (pick i)) hfrontL hrelL
  exact ⟨M, T, hMc, hMconn, hKL.trans hLM, hMR, hM, hT, hTint,
    hBT, hfrontM, hrelM, hprotectM⟩

end PoincareConjecture.M76
