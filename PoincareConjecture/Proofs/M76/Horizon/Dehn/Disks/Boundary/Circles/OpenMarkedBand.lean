import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusDepth

set_option autoImplicit false
open Set PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

theorem exists_open_marked_annulus_band
    {E : Type*} [TopologicalSpace E] {B T S U : Set E} {L d : ℝ}
    (hd : 0 < d) (c : squareAnnulus L d ≃ₜ T)
    (hTB : T ⊆ B) (hST : S ⊆ T)
    (hcore : ∀ p : squareAnnulus L d, (c p : E) ∈ S ↔ depth L p = 0)
    (hU : IsOpen U) (hSU : S ⊆ U) (hUT : U ∩ B ⊆ T) :
    ∃ F O : Set E, IsOpen O ∧ F = B ∩ O ∧
      S ⊆ F ∧ F ⊆ T ∧ F ⊆ B ∧
      IsOpen ((Subtype.val : B → E) ⁻¹' F) ∧
      F = U ∩ ((fun p : squareAnnulus L d => (c p : E)) ''
        {p | depth L p ∈ Ioo (-d) d}) ∧
      ∀ x : T, (x : E) ∈ F → depth L (c.symm x) ∈ Ioo (-d) d := by
  let band : Set (squareAnnulus L d) := {p | depth L p ∈ Ioo (-d) d}
  have hband : IsOpen band := isOpen_Ioo.preimage
    ((continuous_depth L).comp continuous_subtype_val)
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp (c.isOpenMap band hband)
  let F := B ∩ (U ∩ O)
  have hFT : F ⊆ T := fun _ hx => hUT ⟨hx.2.1, hx.1⟩
  have hSF : S ⊆ F := by
    intro x hx
    let p := c.symm ⟨x, hST hx⟩
    have hcp : (c p : E) = x := congrArg Subtype.val (c.apply_symm_apply _)
    have hp0 : depth L p = 0 := (hcore p).mp (hcp.symm ▸ hx)
    have hpband : p ∈ band := by
      change depth L p ∈ Ioo (-d) d
      rw [hp0]
      exact ⟨neg_neg_of_pos hd, hd⟩
    have hxO : x ∈ O := hOeq.symm.subset
      (show (⟨x, hST hx⟩ : T) ∈ c '' band from ⟨p, hpband, c.apply_symm_apply _⟩)
    exact ⟨hTB (hST hx), hSU hx, hxO⟩
  have hopen : IsOpen ((Subtype.val : B → E) ⁻¹' F) := by
    have heq : (Subtype.val : B → E) ⁻¹' F = (Subtype.val : B → E) ⁻¹' (U ∩ O) := by
      ext x
      simp only [mem_preimage, F, mem_inter_iff, x.property, true_and]
    rw [heq]
    exact (hU.inter hO).preimage continuous_subtype_val
  have hinverse (x : T) (hx : (x : E) ∈ F) : depth L (c.symm x) ∈ Ioo (-d) d := by
    obtain ⟨p, hp, hpx⟩ := hOeq.subset (show x ∈ (Subtype.val : T → E) ⁻¹' O from hx.2.2)
    rw [← hpx, c.symm_apply_apply]
    exact hp
  refine ⟨F, U ∩ O, hU.inter hO, rfl, hSF, hFT, inter_subset_left, hopen, ?_, hinverse⟩
  ext x
  constructor
  · intro hx
    exact ⟨hx.2.1, c.symm ⟨x, hFT hx⟩, hinverse ⟨x, hFT hx⟩ hx,
      congrArg Subtype.val (c.apply_symm_apply _)⟩
  · rintro ⟨hxU, p, hp, rfl⟩
    have hxO : (c p : E) ∈ O := hOeq.symm.subset ⟨p, hp, rfl⟩
    exact ⟨hTB (c p).property, hxU, hxO⟩

end PoincareConjecture.M76.Dehn
