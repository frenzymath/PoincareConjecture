import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusReflection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.RimCircleCoordinates

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem exists_planar_annulus_depth_reflection :
    ∃ H : Ann ≃ₜ Ann, H.IsFinitePL ∧ Function.Involutive H ∧
      (∀ x : Ann, depth 8 (H x : P2) = -depth 8 (x : P2)) ∧
      ∀ (b : Bool) (z : Circle), H (annulusRimPoint b z) = annulusRimPoint (!b) z := by
  obtain ⟨H, hH, hdepth, hperiod⟩ :=
    _root_.Dehn.exists_square_annulus_depth_reflection (L := 8) (d := 1)
      (by norm_num) (by norm_num)
  have hinv : Function.Involutive H := by
    intro x
    obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth (L := 8) (d := 1)
      (by norm_num) (by norm_num) x
    let u : Icc (-1 : ℝ) 1 := ⟨depth 8 (x : P2), mem_squareAnnulus_iff_depth.mp x.property⟩
    let v : Icc (-1 : ℝ) 1 := ⟨-(u : ℝ), by
      constructor <;> linarith [u.property.1, u.property.2]⟩
    have hpoint : (⟨annulusMap 8 (by norm_num) ((s : Circle), u),
        _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ u⟩ : Ann) = x :=
      Subtype.ext hsp.symm
    have hHx : H x = ⟨annulusMap 8 (by norm_num) ((s : Circle), v),
        _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ v⟩ := by
      apply Subtype.ext
      rw [← hpoint]
      exact hperiod s hs u
    apply Subtype.ext
    rw [hHx]
    have hh := hperiod s hs v
    change (H _) = annulusMap 8 (by norm_num) ((s : Circle), -(-(u : ℝ))) at hh
    rw [neg_neg] at hh
    exact hh.trans hsp.symm
  refine ⟨H, hH, hinv, hdepth, ?_⟩
  intro b z
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let t := AddCircle.equivIco (4 * (8 : ℝ)) 0 z
  have ht : (t : ℝ) ∈ Icc 0 (4 * (8 : ℝ)) := by
    exact ⟨t.property.1, by simpa only [zero_add] using t.property.2.le⟩
  have htz : ((t : ℝ) : Circle) = z := AddCircle.coe_equivIco
  have hh := hperiod t ht ⟨if b then 1 else -1, by cases b <;> norm_num⟩
  rw [htz] at hh
  apply Subtype.ext
  cases b <;> simpa [annulusRimPoint] using hh

end PoincareConjecture.M76.Dehn
