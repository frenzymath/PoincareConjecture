import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Marked.Coordinates.Rim
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Patches.Pasting

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

local notation "V2" => (Fin 2 → ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "Half" => Icc (-(1 / 2 : ℝ)) (1 / 2)

def rimCylinderReparam (H : Rim ≃ₜ Rim) : rimCylinder ≃ₜ rimCylinder :=
  (Homeomorph.Set.prod Rim Half).trans
    ((H.prodCongr (Homeomorph.refl Half)).trans (Homeomorph.Set.prod Rim Half).symm)

@[simp] theorem rimCylinderReparam_apply (H : Rim ≃ₜ Rim) (x : rimCylinder) :
    (rimCylinderReparam H x : V2 × ℝ) =
      ((H ⟨(x : V2 × ℝ).1, x.property.1⟩ : V2), (x : V2 × ℝ).2) := rfl

@[simp] theorem rimCylinderReparam_symm_apply (H : Rim ≃ₜ Rim) (x : rimCylinder) :
    ((rimCylinderReparam H).symm x : V2 × ℝ) =
      ((H.symm ⟨(x : V2 × ℝ).1, x.property.1⟩ : V2), (x : V2 × ℝ).2) := rfl

theorem rimCylinderReparam_finitePL {H : Rim ≃ₜ Rim} (hH : H.IsFinitePL) :
    (rimCylinderReparam H).IsFinitePL := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show -(1 / 2 : ℝ) < 1 / 2 by norm_num)
  have hid : (Homeomorph.refl Half).IsFinitePL :=
    ⟨id, ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩, fun _ => rfl⟩
  exact hH.prod hid

theorem exists_conjugate_rimCylinder_correction
    (H : Rim ≃ₜ Rim) (hH : H.IsFinitePL)
    (G : rimCylinder ≃ₜ rimCylinder) (hG : G.IsFinitePL)
    (hfixed : ∀ x : rimCylinder, (x : V2 × ℝ).2 = 0 ∨
      (x : V2 × ℝ).2 = -(1 / 2 : ℝ) ∨ (x : V2 × ℝ).2 = 1 / 2 → G x = x) :
    ∃ G' : rimCylinder ≃ₜ rimCylinder, G'.IsFinitePL ∧
      (∀ x : rimCylinder, (x : V2 × ℝ).2 = 0 ∨
        (x : V2 × ℝ).2 = -(1 / 2 : ℝ) ∨ (x : V2 × ℝ).2 = 1 / 2 → G' x = x) ∧
      ∀ x : rimCylinder, G' (rimCylinderReparam H x) = rimCylinderReparam H (G x) := by
  let C := rimCylinderReparam H
  let G' := C.symm.trans (G.trans C)
  have hC : C.IsFinitePL := rimCylinderReparam_finitePL hH
  refine ⟨G', hC.symm.trans (hG.trans hC), ?_, ?_⟩
  · intro x hx
    have hheight : (C.symm x : V2 × ℝ).2 = (x : V2 × ℝ).2 := by
      have h := congrArg (fun y : rimCylinder => (y : V2 × ℝ).2) (C.apply_symm_apply x)
      exact h
    have hfix := hfixed (C.symm x) (hheight.symm ▸ hx)
    change C (G (C.symm x)) = x
    rw [hfix, C.apply_symm_apply]
  · intro x
    change C (G (C.symm (C x))) = C (G x)
    rw [C.symm_apply_apply]

end PoincareConjecture.M76.Dehn.Annuli.RimBands
