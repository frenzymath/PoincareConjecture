import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.PrescribedPhaseShear
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.Orientation.StageRimHomotopy



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "I" => unitInterval

private theorem exists_annulus_unit_twist :
    ∃ T : Ann ≃ₜ Ann, T.IsFinitePL ∧ ∀ (t : I) (z : Circle),
      T (annulusRimCylinder (t, z)) =
        annulusRimCylinder (t, z + ((32 * (t : ℝ) : ℝ) : Circle)) := by
  obtain ⟨T, hT, _, hformula⟩ := exists_annulus_prescribed_phase_shear
    (L := 8) (d := 1) (a₀ := 0) (a₁ := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨T, hT, ?_⟩
  intro t z
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let s : ℝ := AddCircle.equivIco (4 * (8 : ℝ)) 0 z
  have hs : s ∈ Icc 0 (4 * (8 : ℝ)) :=
    ⟨(AddCircle.equivIco _ _ z).property.1,
      by simpa using (AddCircle.equivIco (4 * (8 : ℝ)) 0 z).property.2.le⟩
  have hz : (s : Circle) = z := AddCircle.coe_equivIco
  let u : Icc (-1 : ℝ) 1 :=
    ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.property.1, t.property.2]⟩
  have h := hformula s hs u
  apply Subtype.ext
  change (T ⟨annulusMap 8 (by norm_num) (z, (u : ℝ)), _⟩ : ℝ × ℝ) = _
  rw [← hz, h]
  change annulusMap 8 (by norm_num)
      (((s + (0 + 32) / 2 + (32 - 0) / (2 * 1) * (u : ℝ) : ℝ) : Circle), u) =
    annulusMap 8 (by norm_num) ((s : Circle) + ((32 * (t : ℝ) : ℝ) : Circle), u)
  rw [← AddCircle.coe_add]
  have heq : s + (0 + 32) / 2 + (32 - 0) / (2 * 1) * (u : ℝ) =
      s + 32 * (t : ℝ) := by dsimp [u]; ring
  rw [heq]




theorem exists_integer_annulus_twist (n : ℤ) :
    ∃ T : Ann ≃ₜ Ann, T.IsFinitePL ∧
      (∀ (t : I) (z : Circle), T (annulusRimCylinder (t, z)) =
        annulusRimCylinder (t, z + ((32 * (n : ℝ) * (t : ℝ) : ℝ) : Circle))) ∧
      ∀ side z, T (annulusRimPoint side z) = annulusRimPoint side z := by
  obtain ⟨P, hP, hplus⟩ := exists_annulus_unit_twist
  have hminus (t : I) (z : Circle) : P.symm (annulusRimCylinder (t, z)) =
      annulusRimCylinder (t, z - ((32 * (t : ℝ) : ℝ) : Circle)) := by
    apply P.injective
    rw [P.apply_symm_apply, hplus, sub_add_cancel]
  have htwist (n : ℤ) : ∃ T : Ann ≃ₜ Ann, T.IsFinitePL ∧
      ∀ (t : I) (z : Circle), T (annulusRimCylinder (t, z)) =
        annulusRimCylinder (t, z + ((32 * (n : ℝ) * (t : ℝ) : ℝ) : Circle)) := by
    induction n using Int.induction_on with
    | zero =>
      refine ⟨P.trans P.symm, hP.trans hP.symm, ?_⟩
      intro t z
      simp
    | succ n ih =>
      obtain ⟨T, hT, hTv⟩ := ih
      refine ⟨T.trans P, hT.trans hP, ?_⟩
      intro t z
      change P (T _) = _
      rw [hTv, hplus]
      apply congrArg (fun w : Circle => annulusRimCylinder (t, w))
      rw [add_assoc, ← AddCircle.coe_add]
      apply congrArg (fun r : ℝ => z + (r : Circle))
      push_cast
      ring
    | pred n ih =>
      obtain ⟨T, hT, hTv⟩ := ih
      refine ⟨T.trans P.symm, hT.trans hP.symm, ?_⟩
      intro t z
      change P.symm (T _) = _
      rw [hTv, hminus, sub_eq_add_neg, add_assoc, ← AddCircle.coe_neg,
        ← AddCircle.coe_add]
      apply congrArg (fun w : Circle => annulusRimCylinder (t, w))
      apply congrArg (fun r : ℝ => z + (r : Circle))
      push_cast
      ring
  obtain ⟨T, hT, hTv⟩ := htwist n
  refine ⟨T, hT, hTv, ?_⟩
  intro side z
  cases side
  · simpa using hTv 0 z
  · have hn : ((32 * (n : ℝ) : ℝ) : Circle) = 0 := by
      apply (AddCircle.coe_eq_zero_iff (4 * (8 : ℝ))).mpr
      exact ⟨n, by simp [zsmul_eq_mul]; ring⟩
    simpa [hn] using hTv 1 z

end PoincareConjecture.M76.Dehn
