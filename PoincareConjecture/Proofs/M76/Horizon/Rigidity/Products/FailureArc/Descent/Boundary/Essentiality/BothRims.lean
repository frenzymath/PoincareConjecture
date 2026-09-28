import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.State
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.Orientation.StageRimHomotopy



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "O" => (Set.ofPred (fun x : P2 ↦ x ∈ Ann ∧ depth 8 x = -1))

theorem planarAnnulusRims_nonnull_of_outer
    {X : Type*} [TopologicalSpace X] (original : C(Ann, X))
    (rim : C(O, X)) (hval : ∀ z : O, rim z = original ⟨z, z.property.1⟩)
    (hnon : ¬ rim.Nullhomotopic) :
    ∀ b, ¬ (planarAnnulusRim original b).Nullhomotopic := by
  have houter : ¬ (planarAnnulusRim original false).Nullhomotopic := by
    obtain ⟨H, hHval⟩ := exists_annulus_rim_circle_homeomorph false
    let q : C(O, Circle) :=
      { toFun z := H.symm ⟨⟨z, z.property.1⟩, z.property.2⟩
        continuous_toFun := H.symm.continuous.comp (by fun_prop) }
    have heq : (planarAnnulusRim original false).comp q = rim := by
      apply ContinuousMap.ext
      intro z
      have he : annulusRimPoint false (q z) = (⟨z, z.property.1⟩ : Ann) :=
        (hHval (q z)).symm.trans (congrArg Subtype.val (H.apply_symm_apply _))
      change original (annulusRimPoint false (q z)) = rim z
      rw [he]
      exact (hval z).symm
    intro hnull
    exact hnon (heq ▸ hnull.comp_left q)
  have hom : (planarAnnulusRim original false).Homotopy (planarAnnulusRim original true) :=
    { toFun z := original (annulusRimCylinder z)
      continuous_toFun := original.continuous.comp annulusRimCylinder.continuous
      map_zero_left z := by rw [annulusRimCylinder_zero]; rfl
      map_one_left z := by rw [annulusRimCylinder_one]; rfl }
  intro b
  cases b
  · exact houter
  · rintro ⟨x, hx⟩
    exact houter ⟨x, (show (planarAnnulusRim original false).Homotopic
      (planarAnnulusRim original true) from ⟨hom⟩).trans hx⟩

end PoincareConjecture.M76.Dehn
