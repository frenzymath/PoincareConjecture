import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Disks.TaperingCapAnnuli









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
open PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)



theorem exists_attached_cap_normal_signs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {β : ℝ} (hβ : 0 < β) (τ : C3 → E) (side : Bool)
    (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0) {inner : Set E}
    (hinner : ∀ x ∈ inner, A x = 0)
    (hrim : (fun t => τ ((0, if side then 1 / 2 else -1 / 2), t)) ''
      Icc 0 β ⊆ inner)
    (hzero : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      A (τ x) = 0 ↔ x.1.1 = 0)
    (hsides :
      ((∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β, 0 < x.1.1 → 0 < A (τ x)) ∧
        (∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β, x.1.1 < 0 → A (τ x) < 0)) ∨
      ((∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β, 0 < x.1.1 → A (τ x) < 0) ∧
        (∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β, x.1.1 < 0 → 0 < A (τ x)))) :
    let raw : Bool → Set E := fun positive => inner ∪
      (τ ∘ taperingCapStrip β side positive) '' (Icc 0 (4 * 8) ×ˢ Icc (-1) 1)
    ∃ B : E →ᵃ[ℝ] ℝ,
      B.linear ≠ 0 ∧ (∀ x, B x = 0 ↔ A x = 0) ∧
      (∀ x ∈ raw true, 0 ≤ B x) ∧
      (∀ x ∈ raw false, B x ≤ 0) ∧
      ∀ positive x, x ∈ raw positive → B x = 0 → x ∈ inner := by
  obtain ⟨B, hB, hBA, hpos, hneg⟩ :
      ∃ B : E →ᵃ[ℝ] ℝ, B.linear ≠ 0 ∧ (∀ x, B x = 0 ↔ A x = 0) ∧
        (∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β, 0 < x.1.1 → 0 < B (τ x)) ∧
        (∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β, x.1.1 < 0 → B (τ x) < 0) := by
    rcases hsides with ⟨hp, hn⟩ | ⟨hp, hn⟩
    · exact ⟨A, hA, fun _ => Iff.rfl, hp, hn⟩
    · refine ⟨-A, ?_, ?_, ?_, ?_⟩
      · simpa using hA
      · intro x
        simp
      · intro x hx hs
        exact neg_pos.mpr (hp x hx hs)
      · intro x hx hs
        exact neg_neg_of_pos (hn x hx hs)
  have hBzero (x : C3) (hx : x ∈ signedTubeDiamond ×ˢ Icc 0 β) :
      B (τ x) = 0 ↔ x.1.1 = 0 := (hBA _).trans (hzero x hx)
  have hBinner (x : E) (hx : x ∈ inner) : B x = 0 := (hBA x).mpr (hinner x hx)
  refine ⟨B, hB, hBA, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | ⟨p, hp, rfl⟩
    · exact (hBinner x hx).ge
    · have hm := taperingCapStrip_mapsTo hβ side true hp
      have hs : 0 ≤ (taperingCapStrip β side true p).1.1 := by
        rw [taperingCapStrip_apply]
        simp only [if_true]
        linarith [hp.2.2]
      rcases lt_or_eq_of_le hs with hs | hs
      · exact (hpos _ hm hs).le
      · exact ((hBzero _ hm).mpr hs.symm).ge
  · intro x hx
    rcases hx with hx | ⟨p, hp, rfl⟩
    · exact (hBinner x hx).le
    · have hm := taperingCapStrip_mapsTo hβ side false hp
      have hs : (taperingCapStrip β side false p).1.1 ≤ 0 := by
        rw [taperingCapStrip_apply]
        simp only [Bool.false_eq_true, if_false]
        linarith [hp.2.2]
      rcases lt_or_eq_of_le hs with hs | hs
      · exact (hneg _ hm hs).le
      · exact ((hBzero _ hm).mpr hs).le
  · intro positive x hx hz
    rcases hx with hx | ⟨p, hp, rfl⟩
    · exact hx
    · have hm := taperingCapStrip_mapsTo hβ side positive hp
      have hs := (hBzero _ hm).mp hz
      rw [taperingCapStrip_apply] at hs
      have hu : p.2 = 1 := by
        cases positive <;> simp only [Bool.false_eq_true, if_false, if_true] at hs <;>
          linarith
      apply hrim
      refine ⟨β / 32 * p.1, hm.2, ?_⟩
      change τ _ = τ (taperingCapStrip β side positive p)
      congr 1
      rw [taperingCapStrip_apply, hu]
      cases side <;> cases positive <;> norm_num

end PoincareConjecture.M76
