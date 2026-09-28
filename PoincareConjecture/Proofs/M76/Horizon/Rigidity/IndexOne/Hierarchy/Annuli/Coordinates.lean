import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.Orientation.StageRimHomotopy



set_option autoImplicit false
open Set PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1


noncomputable def annulusCylinderHomeomorph : (unitInterval × Circle) ≃ₜ Ann :=
  (Homeomorph.prodComm unitInterval Circle).trans
    (((Homeomorph.refl Circle).prodCongr
      (iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm).trans
      (exists_annulus_homeomorph (by norm_num : (0 : ℝ) < 8)
        (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : 4 * (1 : ℝ) < 8)).choose)

theorem annulusCylinderHomeomorph_apply (x : unitInterval × Circle) :
    annulusCylinderHomeomorph x = annulusRimCylinder x := by
  apply Subtype.ext
  have h := (exists_annulus_homeomorph (by norm_num : (0 : ℝ) < 8)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : 4 * (1 : ℝ) < 8)).choose_spec
  change ((exists_annulus_homeomorph (by norm_num : (0 : ℝ) < 8)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : 4 * (1 : ℝ) < 8)).choose
      (x.2, (iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm x.1) : ℝ × ℝ) = _
  rw [h, iccHomeoI_symm_apply_coe]
  change annulusMap 8 (by norm_num) (x.2, (1 - -1) * (x.1 : ℝ) + -1) =
    annulusMap 8 (by norm_num) (x.2, 2 * (x.1 : ℝ) - 1)
  congr 2
  ring

@[simp] theorem annulusCylinderHomeomorph_zero (z : Circle) :
    annulusCylinderHomeomorph (0, z) = annulusRimPoint false z := by
  rw [annulusCylinderHomeomorph_apply, annulusRimCylinder_zero]

@[simp] theorem annulusCylinderHomeomorph_one (z : Circle) :
    annulusCylinderHomeomorph (1, z) = annulusRimPoint true z := by
  rw [annulusCylinderHomeomorph_apply, annulusRimCylinder_one]


def annulusRims : Set Ann := range (annulusRimPoint false) ∪ range (annulusRimPoint true)

theorem annulusCylinderHomeomorph_mem_rims (x : unitInterval × Circle) :
    annulusCylinderHomeomorph x ∈ annulusRims ↔ x.1 = 0 ∨ x.1 = 1 := by
  constructor
  · rintro (⟨z, hz⟩ | ⟨z, hz⟩)
    · rw [← annulusCylinderHomeomorph_zero] at hz
      exact Or.inl (congrArg Prod.fst (annulusCylinderHomeomorph.injective hz)).symm
    · rw [← annulusCylinderHomeomorph_one] at hz
      exact Or.inr (congrArg Prod.fst (annulusCylinderHomeomorph.injective hz)).symm
  · rintro (hx | hx)
    · left
      exact ⟨x.2, by rw [← annulusCylinderHomeomorph_zero, ← hx]⟩
    · right
      exact ⟨x.2, by rw [← annulusCylinderHomeomorph_one, ← hx]⟩

end PoincareConjecture.M76.Dehn
