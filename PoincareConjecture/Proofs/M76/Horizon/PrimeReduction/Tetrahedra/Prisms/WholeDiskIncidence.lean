import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.BallPartitionRefinement

set_option autoImplicit false
universe u
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

def HasTwoWholeOwners {E κ : Type*} (B : κ → Set E) (D : Set E) : Prop :=
  ∃ a b, a ≠ b ∧ D ⊆ B a ∧ D ⊆ B b ∧
    ∀ k, k ≠ a → k ≠ b → Disjoint D (B k)

theorem exists_whole_child_avoiding_other
    {E : Type*} [TopologicalSpace E] {B W D : Set E} (C : Bool → Set E)
    (hclosed : ∀ b, IsClosed (C b)) (hunion : C false ∪ C true = B)
    (hinter : C false ∩ C true = W)
    (hD : IsConnected D) (hDB : D ⊆ B) (hDW : Disjoint D W) :
    ∃ b, D ⊆ C b ∧ ∀ c, c ≠ b → Disjoint D (C c) := by
  have hcover : (⋃ b, C b) = B := by
    rw [← hunion]
    ext x
    constructor
    · intro hx
      obtain ⟨b, hb⟩ := mem_iUnion.mp hx
      cases b
      · exact Or.inl hb
      · exact Or.inr hb
    · rintro (hx | hx)
      · exact mem_iUnion.mpr ⟨false, hx⟩
      · exact mem_iUnion.mpr ⟨true, hx⟩
  have hpair : Pairwise fun b c => C b ∩ C c ⊆ W := by
    intro b c hbc
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact hinter.subset
    · exact fun _ hx => hinter.subset ⟨hx.2, hx.1⟩
    · exact (hbc rfl).elim
  obtain ⟨b, hb, _⟩ := exists_unique_disk_owner_away_from_cuts C hclosed hcover
    hpair hD hDB hDW
  refine ⟨b, hb, fun c hcb => disjoint_left.mpr ?_⟩
  intro x hxD hxc
  exact disjoint_left.mp hDW hxD (hpair hcb ⟨hxc, hb hxD⟩)

private theorem two_owners_refine_incident
    {E κ : Type*} [TopologicalSpace E] {B : κ → Set E} {D W : Set E}
    (k l : κ) (hkl : k ≠ l) (C : Bool → Set E)
    (hclosed : ∀ b, IsClosed (C b)) (hunion : C false ∪ C true = B k)
    (hinter : C false ∩ C true = W)
    (hD : IsConnected D) (hk : D ⊆ B k) (hl : D ⊆ B l)
    (hother : ∀ j, j ≠ k → j ≠ l → Disjoint D (B j))
    (hDW : Disjoint D W) :
    HasTwoWholeOwners (Sum.elim (fun j : {j : κ // j ≠ k} => B j) C) D := by
  obtain ⟨b, hb, hmiss⟩ := exists_whole_child_avoiding_other C hclosed hunion hinter hD hk hDW
  refine ⟨Sum.inr b, Sum.inl ⟨l, hkl.symm⟩, Sum.inr_ne_inl, hb, hl, ?_⟩
  intro j hjb hjl
  cases j with
  | inl j =>
    exact hother j j.property (fun he => hjl (congrArg Sum.inl (Subtype.ext he)))
  | inr c => exact hmiss c (fun he => hjb (congrArg Sum.inr he))

theorem HasTwoWholeOwners.refine
    {E κ : Type*} [TopologicalSpace E] {B : κ → Set E} {D W : Set E}
    (howners : HasTwoWholeOwners B D) (k : κ) (C : Bool → Set E)
    (hclosed : ∀ b, IsClosed (C b)) (hunion : C false ∪ C true = B k)
    (hinter : C false ∩ C true = W)
    (hD : IsConnected D) (hDW : Disjoint D W) :
    HasTwoWholeOwners (Sum.elim (fun j : {j : κ // j ≠ k} => B j) C) D := by
  classical
  obtain ⟨a, b, hab, ha, hb, hother⟩ := howners
  by_cases hka : k = a
  · subst a
    exact two_owners_refine_incident k b hab C hclosed hunion hinter hD ha hb hother hDW
  by_cases hkb : k = b
  · subst b
    exact two_owners_refine_incident k a hab.symm C hclosed hunion hinter hD hb ha
      (fun j hjk hja => hother j hja hjk) hDW
  have hCB (c : Bool) : C c ⊆ B k := by
    intro x hx
    apply hunion.subset
    cases c
    · exact Or.inl hx
    · exact Or.inr hx
  refine ⟨Sum.inl ⟨a, Ne.symm hka⟩, Sum.inl ⟨b, Ne.symm hkb⟩, ?_, ha, hb, ?_⟩
  · intro he
    exact hab (congrArg Subtype.val (Sum.inl.inj he))
  · intro j hja hjb
    cases j with
    | inl j =>
      exact hother j (fun he => hja (congrArg Sum.inl (Subtype.ext he)))
        (fun he => hjb (congrArg Sum.inl (Subtype.ext he)))
    | inr c => exact (hother k hka hkb).mono_right (hCB c)

theorem new_cut_has_two_whole_owners
    {E κ : Type*} {B : κ → Set E} {W : Set E} (k : κ) (C : Bool → Set E)
    (hinter : C false ∩ C true = W)
    (hother : ∀ j, j ≠ k → Disjoint W (B j)) :
    HasTwoWholeOwners (Sum.elim (fun j : {j : κ // j ≠ k} => B j) C) W := by
  refine ⟨Sum.inr false, Sum.inr true, by simp,
    hinter.symm.subset.trans inter_subset_left,
    hinter.symm.subset.trans inter_subset_right, ?_⟩
  intro j hjf hjt
  cases j with
  | inl j => exact hother j j.property
  | inr b => cases b <;> contradiction

end PoincareConjecture.M76.PrismBelt
