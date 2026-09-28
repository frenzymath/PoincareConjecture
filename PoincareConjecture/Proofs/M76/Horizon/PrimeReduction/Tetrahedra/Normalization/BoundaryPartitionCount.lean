import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false
namespace PoincareConjecture.M76

theorem boundary_partition_excess_mono
    {ρ α : Type*} [DecidableEq ρ] [DecidableEq α]
    (rims retained : Finset ρ) (hretained : retained ⊆ rims) (owner : ρ → α) :
    retained.card - (retained.image owner).card ≤ rims.card - (rims.image owner).card := by
  have hcover : rims.image owner ⊆ retained.image owner ∪ (rims \ retained).image owner := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    by_cases hir : i ∈ retained
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem owner hir)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem owner (Finset.mem_sdiff.mpr ⟨hi,hir⟩))
  have hle := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hdiff := Finset.card_image_le (s := rims \ retained) (f := owner)
  have hsub := Finset.card_sdiff_add_card_eq_card hretained
  have hbound := Finset.card_image_le (s := retained) (f := owner)
  omega

theorem boundary_partition_excess_le_of_refinement
    {ρ α β : Type*} [DecidableEq ρ] [DecidableEq α] [DecidableEq β]
    (rims retained : Finset ρ) (hretained : retained ⊆ rims)
    (old : ρ → α) (new : ρ → β)
    (hrefine : ∀ i ∈ retained, ∀ j ∈ retained, new i = new j → old i = old j) :
    retained.card - (retained.image new).card ≤ rims.card - (rims.image old).card := by
  classical
  by_cases hne : retained.Nonempty
  · obtain ⟨a,ha⟩ := hne
    let parent : β → α := fun d => if h : ∃ i ∈ retained, new i = d then old h.choose else old a
    have hparent (i : ρ) (hi : i ∈ retained) : parent (new i) = old i := by
      have h : ∃ j ∈ retained, new j = new i := ⟨i,hi,rfl⟩
      simp only [parent,dif_pos h]
      exact hrefine h.choose h.choose_spec.1 i hi h.choose_spec.2
    have himage : (retained.image new).image parent = retained.image old := by
      rw [Finset.image_image]
      exact Finset.image_congr (fun i hi => hparent i hi)
    have hle := Finset.card_image_le (s := retained.image new) (f := parent)
    rw [himage] at hle
    exact (Nat.sub_le_sub_left hle _).trans (boundary_partition_excess_mono rims retained hretained old)
  · simp only [Finset.not_nonempty_iff_eq_empty] at hne
    simp [hne]

theorem boundary_partition_excess_lt_of_split
    {ρ α β : Type*} [DecidableEq α] [DecidableEq β]
    (rims : Finset ρ) (old : ρ → α) (new : ρ → β)
    (hrefine : ∀ i ∈ rims, ∀ j ∈ rims, new i = new j → old i = old j)
    {a b : ρ} (ha : a ∈ rims) (hb : b ∈ rims)
    (hsame : old a = old b) (hsplit : new a ≠ new b) :
    rims.card - (rims.image new).card < rims.card - (rims.image old).card := by
  classical
  let parent : β → α := fun d => if h : ∃ i ∈ rims, new i = d then
    old h.choose else old a
  have hparent (i : ρ) (hi : i ∈ rims) : parent (new i) = old i := by
    have h : ∃ j ∈ rims, new j = new i := ⟨i,hi,rfl⟩
    simp only [parent,dif_pos h]
    exact hrefine h.choose h.choose_spec.1 i hi h.choose_spec.2
  have himage : (rims.image new).image parent = rims.image old := by
    rw [Finset.image_image]
    exact Finset.image_congr (fun i hi => hparent i hi)
  have hne : ((rims.image new).image parent).card ≠ (rims.image new).card := by
    intro hcard
    have hinj := Finset.card_image_iff.mp hcard
    apply hsplit
    exact hinj (Finset.mem_image_of_mem new ha) (Finset.mem_image_of_mem new hb)
      ((hparent a ha).trans (hsame.trans (hparent b hb).symm))
  have hle := Finset.card_image_le (s := rims.image new) (f := parent)
  have hbound := Finset.card_image_le (s := rims) (f := new)
  rw [himage] at hne hle
  omega

theorem boundary_partition_excess_lt_of_isolated_rim
    {ρ α β : Type*} [DecidableEq ρ] [DecidableEq α] [DecidableEq β]
    (rims retained : Finset ρ) (hretained : retained ⊆ rims)
    (old : ρ → α) (new : ρ → β)
    (hrefine : ∀ i ∈ retained, ∀ j ∈ retained, new i = new j → old i = old j)
    {a b : ρ} (ha : a ∈ rims) (hb : b ∈ rims) (hab : a ≠ b)
    (hsame : old a = old b)
    (hisolate : a ∈ retained → ∀ i ∈ retained, new i = new a → i = a) :
    retained.card - (retained.image new).card < rims.card - (rims.image old).card := by
  classical
  let extended : ρ → β ⊕ ρ := fun i => if i ∈ retained then .inl (new i) else .inr i
  have hExtRef : ∀ i ∈ rims, ∀ j ∈ rims, extended i = extended j → old i = old j := by
    intro i hi j hj hij
    by_cases hir : i ∈ retained <;> by_cases hjr : j ∈ retained
    · exact hrefine i hir j hjr (by simpa [extended,hir,hjr] using hij)
    · simp [extended,hir,hjr] at hij
    · simp [extended,hir,hjr] at hij
    · have heq : i = j := by simpa [extended,hir,hjr] using hij
      rw [heq]
  have hExtSplit : extended a ≠ extended b := by
    intro heq
    by_cases har : a ∈ retained <;> by_cases hbr : b ∈ retained
    · have hn : new b = new a := by simpa [extended,har,hbr] using heq.symm
      exact hab (hisolate har b hbr hn).symm
    · simp [extended,har,hbr] at heq
    · simp [extended,har,hbr] at heq
    · exact hab (by simpa [extended,har,hbr] using heq)
  have hlt := boundary_partition_excess_lt_of_split rims old extended hExtRef ha hb hsame hExtSplit
  have hparts : rims.image extended =
      (retained.image new).image Sum.inl ∪ (rims \ retained).image Sum.inr := by
    ext y
    constructor
    · intro hy
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
      by_cases hir : i ∈ retained
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨new i,Finset.mem_image_of_mem new hir,by simp [extended,hir]⟩
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨i,Finset.mem_sdiff.mpr ⟨hi,hir⟩,by simp [extended,hir]⟩
    · intro hy
      rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
        exact Finset.mem_image.mpr ⟨i,hretained hi,by simp [extended,hi]⟩
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
        have hi' := Finset.mem_sdiff.mp hi
        exact Finset.mem_image.mpr ⟨i,hi'.1,by simp [extended,hi'.2]⟩
  have hdis : Disjoint ((retained.image new).image (Sum.inl : β → β ⊕ ρ))
      ((rims \ retained).image Sum.inr) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hz
    obtain ⟨y,_,hy⟩ := Finset.mem_image.mp hz'
    exact Sum.inl_ne_inr (hx.trans hy.symm)
  have hcount : (rims.image extended).card = (retained.image new).card + (rims \ retained).card := by
    rw [hparts,Finset.card_union_of_disjoint hdis,
      Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective]
  have hsub := Finset.card_sdiff_add_card_eq_card hretained
  have hbound := Finset.card_image_le (s := retained) (f := new)
  rw [hcount] at hlt
  omega

end PoincareConjecture.M76
