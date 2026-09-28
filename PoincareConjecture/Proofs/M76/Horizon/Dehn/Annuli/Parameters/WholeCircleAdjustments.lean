import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.PeriodReflection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.PrescribedPhaseShear








set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "C" => AddCircle (4 * (8 : ℝ))
local notation "A" => squareAnnulus 8 1

noncomputable def annulusRimPoint (b : Bool) (z : C) : A :=
  ⟨annulusMap 8 (by norm_num) (z, if b then 1 else -1),
    _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) z
      ⟨if b then 1 else -1, by cases b <;> norm_num⟩⟩

theorem exists_annulus_whole_rim_reflection :
    ∃ R : A ≃ₜ A, R.IsFinitePL ∧
      ∀ (b : Bool) (z : C), R (annulusRimPoint b z) = annulusRimPoint b (-z) := by
  obtain ⟨R, hR, hv⟩ := exists_annulus_period_reflection (L := 8) (d := 1)
    (by norm_num) (by norm_num)
  refine ⟨R, hR, ?_⟩
  intro b z
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let s : ℝ := AddCircle.equivIco (4 * (8 : ℝ)) 0 z
  have hs : s ∈ Icc 0 (4 * 8) :=
    ⟨(AddCircle.equivIco (4 * (8 : ℝ)) 0 z).property.1,
      by simpa only [zero_add] using (AddCircle.equivIco (4 * (8 : ℝ)) 0 z).property.2.le⟩
  have hsz : (s : C) = z := AddCircle.coe_equivIco
  have hh := hv s hs ⟨if b then 1 else -1, by cases b <;> norm_num⟩
  rw [hsz] at hh
  exact Subtype.ext hh

theorem exists_annulus_whole_rim_phases (a : Bool → ℝ)
    (ha : ∀ b, a b ∈ Icc 0 32) :
    ∃ S : A ≃ₜ A, S.IsFinitePL ∧
      ∀ (b : Bool) (z : C), S (annulusRimPoint b z) =
        annulusRimPoint b (z + ((a b : ℝ) : C)) := by
  have ha' (b : Bool) : a b ∈ Icc 0 (4 * (8 : ℝ)) := by norm_num; exact ha b
  obtain ⟨S, hS, _, hv⟩ := exists_annulus_prescribed_phase_shear (L := 8) (d := 1)
    (by norm_num) (by norm_num) (ha' false) (ha' true)
  refine ⟨S, hS, ?_⟩
  intro b z
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let s : ℝ := AddCircle.equivIco (4 * (8 : ℝ)) 0 z
  have hs : s ∈ Icc 0 (4 * 8) :=
    ⟨(AddCircle.equivIco (4 * (8 : ℝ)) 0 z).property.1,
      by simpa only [zero_add] using (AddCircle.equivIco (4 * (8 : ℝ)) 0 z).property.2.le⟩
  have hsz : (s : C) = z := AddCircle.coe_equivIco
  have hh := hv s hs ⟨if b then 1 else -1, by cases b <;> norm_num⟩
  have heq : s + (a false + a true) / 2 + (a true - a false) / (2 * 1) *
      (if b then 1 else -1) = s + a b := by cases b <;> norm_num <;> ring
  simp only [heq, AddCircle.coe_add, hsz] at hh
  exact Subtype.ext hh

end PoincareConjecture.M76.Dehn
