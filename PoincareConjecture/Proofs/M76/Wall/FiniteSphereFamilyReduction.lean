import PoincareConjecture.Proofs.M76.Wall.OriginalFilledSphereAttachment
import PoincareConjecture.Proofs.M76.Wall.IndexedSphericalFilling

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_smaller_filled_spherical_family
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R L P : Set X}
    (hR : PLDomain e R) (hRconn : IsConnected R) (hend : HasOneSimplyConnectedEnd R)
    (hL : PLDomain e L) (hLc : IsCompact L) (hLconn : IsConnected L) (hLR : L ⊆ R)
    (hP : IsClosed P) (hPR : P ⊆ R) (hBP : frontier R ⊆ P)
    (hprotect : (Subtype.val : R → X) ⁻¹' P ⊆
      interior ((Subtype.val : R → X) ⁻¹' L))
    (hcompl : IsConnected (((Subtype.val : R → X) ⁻¹' L)ᶜ))
    (S : κ → Set X) (hS : ∀ i, Nonempty (ChartwisePLSphere e (S i)))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (hSint : ∀ i, S i ⊆ interior R)
    (hfront : frontier L = frontier R ∪ ⋃ i, S i)
    (a b : κ) (hab : a ≠ b) :
    ∃ (Lnew : Set X) (m : ℕ) (Snew : Fin m → Set X),
      0 < m ∧ m < Nat.card κ ∧ IsCompact Lnew ∧ IsConnected Lnew ∧
      L ⊆ Lnew ∧ Lnew ⊆ R ∧ PLDomain e Lnew ∧
      (∀ i, Nonempty (ChartwisePLSphere e (Snew i))) ∧
      (Pairwise fun i j => Disjoint (Snew i) (Snew j)) ∧
      (∀ i, Snew i ⊆ interior R) ∧
      frontier Lnew = frontier R ∪ ⋃ i, Snew i ∧
      frontier ((Subtype.val : R → X) ⁻¹' Lnew) =
        (Subtype.val : R → X) ⁻¹' (⋃ i, Snew i) ∧
      IsConnected (((Subtype.val : R → X) ⁻¹' Lnew)ᶜ) ∧
      (Subtype.val : R → X) ⁻¹' P ⊆ interior ((Subtype.val : R → X) ⁻¹' Lnew) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  let Rest := {i : κ // i ≠ a ∧ i ≠ b}
  let F : Set X := ⋃ i : Rest, S i.val
  let pair : Fin 2 → Set X := Fin.cases (S a) (fun _ => S b)
  have hFclosed : IsClosed F :=
    isClosed_iUnion_of_finite fun i : Rest =>
      (Classical.choice (hS i.val)).compact_connected.1.isClosed
  have hFint : F ⊆ interior R := iUnion_subset fun i : Rest => hSint i.val
  have hpair (i : Fin 2) : Nonempty (ChartwisePLSphere e (pair i)) := by
    fin_cases i
    · exact hS a
    · exact hS b
  have hpairint (i : Fin 2) : pair i ⊆ interior R := by
    fin_cases i
    · exact hSint a
    · exact hSint b
  have hpairdisj : Pairwise fun i j => Disjoint (pair i) (pair j) := by
    intro i j hij
    fin_cases i
    · fin_cases j
      · exact False.elim (hij rfl)
      · exact hdisjoint hab
    · fin_cases j
      · exact (hdisjoint hab).symm
      · exact False.elim (hij rfl)
  have hFa : Disjoint F (S a) := by
    apply disjoint_left.mpr
    intro x hxF hxa
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxF
    exact disjoint_left.mp (hdisjoint i.property.1) hi hxa
  have hFb : Disjoint F (S b) := by
    apply disjoint_left.mpr
    intro x hxF hxb
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxF
    exact disjoint_left.mp (hdisjoint i.property.2) hi hxb
  have hFpair (i : Fin 2) : Disjoint F (pair i) := by
    fin_cases i
    · exact hFa
    · exact hFb
  have hunion : (⋃ i, S i) = F ∪ (S a ∪ S b) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      by_cases hia : i = a
      · exact Or.inr (Or.inl (hia ▸ hi))
      by_cases hib : i = b
      · exact Or.inr (Or.inr (hib ▸ hi))
      exact Or.inl (mem_iUnion.mpr ⟨⟨i, hia, hib⟩, hi⟩)
    · rintro (hxF | hxa | hxb)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hxF
        exact mem_iUnion.mpr ⟨i.val, hi⟩
      · exact mem_iUnion.mpr ⟨a, hxa⟩
      · exact mem_iUnion.mpr ⟨b, hxb⟩
  have hfront' : frontier L = (frontier R ∪ F) ∪ (pair 0 ∪ pair 1) := by
    change frontier L = (frontier R ∪ F) ∪ (S a ∪ S b)
    rw [hfront, hunion, union_assoc]
  obtain ⟨K, T, hKc, hKconn, hLK, hKR, _, hK, hT, hTint, hFT, hfr, hrel, hprot, _⟩ :=
    hR.exists_filled_two_sphere_attachment hL hLc hLconn hLR hP hPR hBP
      hprotect hcompl hFclosed hFint pair (fun i => Classical.choice (hpair i))
      hpairint hpairdisj hFpair hfront'
  let New := Option Rest
  let S' : New → Set X
    | none => T
    | some i => S i.val
  have hS' (i : New) : Nonempty (ChartwisePLSphere e (S' i)) := by
    cases i with
    | none => exact hT
    | some i => exact hS i.val
  have hS'int (i : New) : S' i ⊆ interior R := by
    cases i with
    | none => exact hTint
    | some i => exact hSint i.val
  have hS'disj : Pairwise fun i j => Disjoint (S' i) (S' j) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j => exact hFT.symm.mono subset_rfl (subset_iUnion (fun i : Rest => S i.val) j)
    | some i =>
      cases j with
      | none => exact hFT.mono (subset_iUnion (fun j : Rest => S j.val) i) subset_rfl
      | some j =>
        exact hdisjoint (fun h => hij (congrArg some (Subtype.ext h)))
  have hnewunion : (⋃ i, S' i) = F ∪ T := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      cases i with
      | none => exact Or.inr hi
      | some i => exact Or.inl (mem_iUnion.mpr ⟨i, hi⟩)
    · rintro (hxF | hxT)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hxF
        exact mem_iUnion.mpr ⟨some i, hi⟩
      · exact mem_iUnion.mpr ⟨none, hxT⟩
  have hfrontK : frontier K = frontier R ∪ ⋃ i, S' i := by
    rw [hnewunion]
    exact hfr
  have hrelK : frontier ((Subtype.val : R → X) ⁻¹' K) =
      (Subtype.val : R → X) ⁻¹' (⋃ i, S' i) := by
    rw [hnewunion]
    exact hrel
  let oldIndex : New → κ
    | none => a
    | some i => i.val
  have hinj : Function.Injective oldIndex := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => exact False.elim (j.property.1 hij.symm)
    | some i =>
      cases j with
      | none => exact False.elim (i.property.1 hij)
      | some j => exact congrArg some (Subtype.ext hij)
  have hmiss : b ∉ range oldIndex := by
    rintro ⟨i, hi⟩
    cases i with
    | none => exact hab hi
    | some i => exact i.property.2 hi
  have hcard : Nat.card New < Nat.card κ := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_lt_of_injective_of_notMem oldIndex hinj hmiss
  obtain ⟨Lnew, m, pick, hm, hbound, hLc', hLconn', hKLnew, hLnewR,
    hLnew, hfrontNew, hrelNew, hcomplNew, hprotectNew⟩ :=
    exists_indexed_spherical_frontier_filling hR hRconn hend hK hKc hKconn hKR
      S' hS' hS'disj hS'int hfrontK hrelK hBP hprot
  exact ⟨Lnew, m, fun i => S' (pick i), hm, hbound.trans_lt hcard,
    hLc', hLconn', hLK.trans hKLnew, hLnewR, hLnew, fun i => hS' (pick i),
    fun _ _ hij => hS'disj (fun h => hij (pick.injective h)),
    fun i => hS'int (pick i), hfrontNew, hrelNew, hcomplNew, hprotectNew⟩

end PoincareConjecture.M76
