import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.WholeCircleAdjustments

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

theorem continuous_annulusRimPoint (b : Bool) : Continuous (annulusRimPoint b) := by
  apply Continuous.subtype_mk
  have h := continuous_annulusMap (L := 8) (d := 1) (by norm_num) (by norm_num)
  exact h.comp (continuous_id.prodMk
    (continuous_const (y := (⟨if b then 1 else -1, by cases b <;> norm_num⟩ : Icc (-1 : ℝ) 1))))

theorem injective_annulusRimPoint (b : Bool) : Function.Injective (annulusRimPoint b) := by
  intro z w h
  exact congrArg Prod.fst (injective_annulusMap (L := 8) (d := 1)
    (by norm_num) (by norm_num)
    (a₁ := (z, ⟨if b then 1 else -1, by cases b <;> norm_num⟩))
    (a₂ := (w, ⟨if b then 1 else -1, by cases b <;> norm_num⟩))
    (congrArg Subtype.val h))

theorem depth_annulusRimPoint (b : Bool) (z : Circle) :
    depth 8 (annulusRimPoint b z : P2) = if b then 1 else -1 := by
  exact depth_annulusMap (by norm_num) (by cases b <;> norm_num) z

theorem range_annulusRimPoint (b : Bool) :
    range (annulusRimPoint b) = {x : Ann | depth 8 (x : P2) = if b then 1 else -1} := by
  apply Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    exact depth_annulusRimPoint b z
  · intro x hx
    obtain ⟨s, hs, hv⟩ := exists_period_parameter_of_depth (L := 8) (d := 1)
      (by norm_num) (by norm_num) x
    refine ⟨(s : Circle), Subtype.ext ?_⟩
    change annulusMap 8 (by norm_num) ((s : Circle), if b then 1 else -1) = (x : P2)
    rw [← hx]
    exact hv.symm

theorem exists_annulus_rim_circle_homeomorph (b : Bool) :
    ∃ R : Circle ≃ₜ {x : Ann | depth 8 (x : P2) = if b then 1 else -1},
      ∀ z, (R z : Ann) = annulusRimPoint b z := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  have h := (continuous_annulusRimPoint b).isClosedEmbedding (injective_annulusRimPoint b)
  exact ⟨h.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr (range_annulusRimPoint b)),
    fun _ ↦ rfl⟩

end PoincareConjecture.M76.Dehn
