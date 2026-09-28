import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalClosedBallDiskCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Cutting.DiskPartitionRefinement
import Mathlib.SetTheory.Cardinal.NatCard









set_option autoImplicit false
universe u
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_proper_disk_ball_partition_refinement
    {E : Type*} {κ : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite κ]
    {S Q T W q : Set E} (B R : κ → Set E)
    (hB : ∀ k, IsFinitePLBallPair V3 (B k) (R k))
    (hR : ∀ k, R k = B k ∩ (Q ∪ T))
    (hcover : (⋃ k, B k) = S)
    (hinter : Pairwise fun k l => B k ∩ B l ⊆ T)
    (hW : IsFinitePLBallPair (ℝ × ℝ) W q)
    (hWS : W ⊆ S) (hWrim : W ∩ Q = q) (hWT : Disjoint W T) :
    ∃ κ' : Type u, Finite κ' ∧ ∃ B' R' : κ' → Set E,
      Nat.card κ' = Nat.card κ + 1 ∧
      (∀ k, IsFinitePLBallPair V3 (B' k) (R' k)) ∧
      (∀ k, R' k = B' k ∩ (Q ∪ (T ∪ W))) ∧
      (⋃ k, B' k) = S ∧
      Pairwise (fun k l => B' k ∩ B' l ⊆ T ∪ W) := by
  classical
  let := Fintype.ofFinite κ
  obtain ⟨k,hWB,_⟩ := exists_unique_disk_owner_away_from_cuts B
    (fun l => (hB l).isCompact.isClosed) hcover hinter hW.isConnected hWS hWT
  have hproper : W ∩ R k = q := by
    rw [hR k,←hWrim]
    ext x
    constructor
    · rintro ⟨hxW,hxB,hxQ | hxT⟩
      · exact ⟨hxW,hxQ⟩
      · exact (disjoint_left.mp hWT hxW hxT).elim
    · intro hx
      exact ⟨hx.1,hWB hx.1,Or.inl hx.2⟩
  obtain ⟨C,hC,hCunion,hCinter⟩ := exists_original_closed_ball_disk_cut (hB k) hW hWB hproper
  have hCB (b : Bool) : C b ⊆ B k := by
    intro x hx
    apply hCunion.subset
    cases b
    · exact Or.inl hx
    · exact Or.inr hx
  have hWC (b : Bool) : W ⊆ C b := by
    intro x hx
    have hh := hCinter.symm.subset hx
    cases b
    · exact hh.1
    · exact hh.2
  have hother (l : {l : κ // l ≠ k}) : Disjoint (B l) W := by
    apply disjoint_left.mpr
    intro x hxl hxW
    exact disjoint_left.mp hWT hxW (hinter l.property ⟨hxl,hWB hxW⟩)
  let κ' := {l : κ // l ≠ k} ⊕ Bool
  let B' : κ' → Set E := Sum.elim (fun l => B l) C
  let R' : κ' → Set E := fun z => B' z ∩ (Q ∪ (T ∪ W))
  have hnew (b : Bool) : R' (Sum.inr b) = (C b ∩ R k) ∪ W := by
    change C b ∩ (Q ∪ (T ∪ W)) = _
    rw [hR k]
    ext x
    have hc := @hCB b x
    have hw := @hWC b x
    simp only [mem_inter_iff,mem_union]
    tauto
  have hold (l : {l : κ // l ≠ k}) : R' (Sum.inl l) = R l := by
    change B l ∩ (Q ∪ (T ∪ W)) = _
    rw [hR l]
    ext x
    have hmiss : x ∈ B l → x ∉ W := fun hx => disjoint_left.mp (hother l) hx
    simp only [mem_inter_iff,mem_union]
    tauto
  refine ⟨κ',inferInstance,B',R',?_,?_,fun _ => rfl,?_,?_⟩
  · have hc : Fintype.card {l : κ // l ≠ k} = Fintype.card κ - 1 := by
      simpa using Fintype.card_subtype_compl (fun l : κ => l = k)
    have hpos : 0 < Fintype.card κ := Fintype.card_pos_iff.mpr ⟨k⟩
    simp only [κ',Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_bool,hc]
    omega
  · intro z
    cases z with
    | inl l => simpa only [hold,B',Sum.elim_inl] using hB l
    | inr b => simpa only [hnew,B',Sum.elim_inr] using hC b
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨z,hz⟩ := mem_iUnion.mp hx
      apply hcover.subset
      cases z with
      | inl l => exact mem_iUnion.mpr ⟨l,hz⟩
      | inr b => exact mem_iUnion.mpr ⟨k,hCB b hz⟩
    · intro x hx
      obtain ⟨l,hl⟩ := mem_iUnion.mp (hcover.symm.subset hx)
      by_cases hlk : l = k
      · rcases hCunion.symm.subset (hlk ▸ hl) with h0 | h1
        · exact mem_iUnion.mpr ⟨Sum.inr false,h0⟩
        · exact mem_iUnion.mpr ⟨Sum.inr true,h1⟩
      · exact mem_iUnion.mpr ⟨Sum.inl ⟨l,hlk⟩,hl⟩
  · intro z w hzw x hx
    cases z with
    | inl l =>
      cases w with
      | inl m =>
        have hlm : (l : κ) ≠ m := fun he => hzw (congrArg Sum.inl (Subtype.ext he))
        exact Or.inl (hinter hlm hx)
      | inr b => exact Or.inl (hinter l.property ⟨hx.1,hCB b hx.2⟩)
    | inr b =>
      cases w with
      | inl l => exact Or.inl (hinter l.property ⟨hx.2,hCB b hx.1⟩)
      | inr c =>
        apply Or.inr
        cases b <;> cases c
        · exact (hzw rfl).elim
        · exact hCinter.subset hx
        · exact hCinter.subset ⟨hx.2,hx.1⟩
        · exact (hzw rfl).elim

end PoincareConjecture.M76
