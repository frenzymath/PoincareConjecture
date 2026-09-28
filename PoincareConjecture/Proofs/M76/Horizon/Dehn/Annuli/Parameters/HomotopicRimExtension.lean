import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.PrescribedIntervalRims
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.WholeCircleAdjustments
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.SignedIntervalRim
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.Orientation.HomotopySigns









set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "I" => Icc (0 : ℝ) 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

private theorem exists_signed_rim_extension (positive : Bool)
    (a : Bool → ℝ) (ha : ∀ b, a b ∈ Icc 0 32)
    (e : Bool → I ≃ₜ I) (he : ∀ b, (e b).IsFinitePL)
    (h0 : ∀ b, (e b ⟨0, by norm_num⟩ : ℝ) = 0)
    (h1 : ∀ b, (e b ⟨1, by norm_num⟩ : ℝ) = 1) :
    ∃ H : Ann ≃ₜ Ann, H.IsFinitePL ∧ ∀ (b : Bool) (s : I),
      H (annulusRimPoint b ((32 * (s : ℝ) : ℝ) : Circle)) =
        annulusRimPoint b (((a b +
          (if positive then 32 * (e b s : ℝ) else -(32 * (e b s : ℝ)))) : ℝ) : Circle) := by
  obtain ⟨A, hA, hAv⟩ := exists_annulus_homeomorph_prescribed_interval_rims e he h0 h1
  have hAv' (b : Bool) (s : I) :
      A (annulusRimPoint b ((32 * (s : ℝ) : ℝ) : Circle)) =
        annulusRimPoint b ((32 * (e b s : ℝ) : ℝ) : Circle) := Subtype.ext (hAv b s)
  obtain ⟨S, hS, hSv⟩ := exists_annulus_whole_rim_phases a ha
  cases positive
  · obtain ⟨R, hR, hRv⟩ := exists_annulus_whole_rim_reflection
    refine ⟨A.trans (R.trans S), hA.trans (hR.trans hS), ?_⟩
    intro b s
    change S (R (A _)) = _
    rw [hAv', hRv, hSv]
    simp only [Bool.false_eq_true, ↓reduceIte, AddCircle.coe_add, AddCircle.coe_neg, add_comm]
  · refine ⟨A.trans S, hA.trans hS, ?_⟩
    intro b s
    change S (A _) = _
    rw [hAv', hSv]
    simp only [↓reduceIte, AddCircle.coe_add, add_comm]

theorem exists_annulus_homotopic_rim_extension (q : Bool → Circle ≃ₜ Circle)
    (H : (⟨q false, (q false).continuous⟩ : C(Circle, Circle)).Homotopy
      ⟨q true, (q true).continuous⟩)
    (hq : ∀ b, FinitePiecewiseAffineOn (fun s : ℝ ↦ annulusMap 8 (by norm_num)
      (q b ((32 * s : ℝ) : Circle), if b then 1 else -1)) I) :
    ∃ A : Ann ≃ₜ Ann, A.IsFinitePL ∧
      ∀ (b : Bool) (z : Circle), A (annulusRimPoint b z) = annulusRimPoint b (q b z) := by
  classical
  have hi (b : Bool) := exists_signed_interval_rim (q b)
    (u := if b then 1 else -1) (by cases b <;> norm_num) (hq b)
  choose a positive e ha he h0 h1 hv using hi
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  have hsign : positive false = positive true :=
    AddCircle.signed_interval_formulas_same_sign
      ⟨q false, (q false).continuous⟩ ⟨q true, (q true).continuous⟩ H
      (a false) (a true) (positive false) (positive true)
      ⟨e false, (e false).continuous⟩ ⟨e true, (e true).continuous⟩
      (h0 false) (h1 false) (h0 true) (h1 true)
      (by intro s; convert hv false s using 1 <;> norm_num)
      (by intro s; convert hv true s using 1 <;> norm_num)
  obtain ⟨A, hA, hAv⟩ := exists_signed_rim_extension (positive false) a
    (fun b ↦ ⟨(ha b).1, (ha b).2.le⟩) e he h0 h1
  refine ⟨A, hA, ?_⟩
  intro b z
  let t : ℝ := AddCircle.equivIco (4 * (8 : ℝ)) 0 z
  have ht : t ∈ Icc 0 32 := by
    have hh := (AddCircle.equivIco (4 * (8 : ℝ)) 0 z).property
    change 0 ≤ t ∧ t < 0 + 4 * 8 at hh
    norm_num at hh
    exact ⟨hh.1, hh.2.le⟩
  have htz : (t : Circle) = z := AddCircle.coe_equivIco
  let s : I := ⟨t / 32, by constructor <;> linarith [ht.1, ht.2]⟩
  have hs : 32 * (s : ℝ) = t := by dsimp [s]; ring
  have hsb : positive false = positive b := by cases b; rfl; exact hsign
  have hh := hAv b s
  rw [hsb, ← hv b s, hs, htz] at hh
  exact hh

end PoincareConjecture.M76.Dehn
