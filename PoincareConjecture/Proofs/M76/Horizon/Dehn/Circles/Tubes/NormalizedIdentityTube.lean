import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.PeriodicCoordinates








set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

theorem normalized_identity_tube_fibers
    {X : Type*} {L d α β : ℝ} (hL : 0 < L) (hd : 0 < d) (hab : α < β)
    (τ : C3 → X)
    (hfib : ∀ x ∈ signedTubeDiamond ×ˢ Icc α β,
      ∀ y ∈ signedTubeDiamond ×ˢ Icc α β,
      τ x = τ y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = α ∧ y.2 = β) ∨ (x.2 = β ∧ y.2 = α))) :
    ∀ z ∈ _root_.Dehn.identityTube L d, ∀ w ∈ _root_.Dehn.identityTube L d,
      (τ ∘ periodicTubeCoordinates L d α β) z =
        (τ ∘ periodicTubeCoordinates L d α β) w ↔
      z.1 = w.1 ∧ (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)) := by
  intro z hz w hw
  let : Fact (0 < 4 * L) := ⟨by positivity⟩
  have hp : 0 < 4 * L := by positivity
  have hc : 0 < (β - α) / (4 * L) := div_pos (sub_pos.mpr hab) hp
  have hcp : ((β - α) / (4 * L)) * (4 * L) = β - α := div_mul_cancel₀ _ hp.ne'
  have hxy : (periodicTubeCoordinates L d α β z).1 =
      (periodicTubeCoordinates L d α β w).1 ↔ z.1 = w.1 := by
    change signedSquareToDiamond (d⁻¹ • z.1) =
      signedSquareToDiamond (d⁻¹ • w.1) ↔ _
    exact signedSquareToDiamond.injective.eq_iff.trans
      (smul_right_injective _ (inv_ne_zero hd.ne')).eq_iff
  have htime (s t : ℝ) :
      α + ((β - α) / (4 * L)) * s = α + ((β - α) / (4 * L)) * t ↔ s = t :=
    add_left_cancel_iff.trans (mul_right_inj' hc.ne')
  have hstart (s : ℝ) : α + ((β - α) / (4 * L)) * s = α ↔ s = 0 := by
    simpa only [mul_zero, add_zero] using htime s 0
  have hend (s : ℝ) : α + ((β - α) / (4 * L)) * s = β ↔ s = 4 * L := by
    have h := htime s (4 * L)
    simpa only [hcp, add_sub_cancel] using h
  rw [Function.comp_apply, Function.comp_apply,
    hfib _ (periodicTubeCoordinates_mapsTo hL hd hab hz)
      _ (periodicTubeCoordinates_mapsTo hL hd hab hw), hxy,
    AddCircle.coe_eq_coe_iff_eq_or_endpoints hz.2 hw.2]
  change z.1 = w.1 ∧
    ((α + ((β - α) / (4 * L)) * z.2 = α + ((β - α) / (4 * L)) * w.2) ∨
      (α + ((β - α) / (4 * L)) * z.2 = α ∧
        α + ((β - α) / (4 * L)) * w.2 = β) ∨
      (α + ((β - α) / (4 * L)) * z.2 = β ∧
        α + ((β - α) / (4 * L)) * w.2 = α)) ↔ _
  rw [htime, hstart, hend, hend, hstart]



theorem exists_normalized_identity_tube
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L d α β : ℝ} (hL : 0 < L) (hd : 0 < d) (hab : α < β)
    (τ : C3 → E) (hτ : FinitePiecewiseAffineOn τ (signedTubeDiamond ×ˢ Icc α β))
    (S : Fin 2 → Set E)
    (hsheet : ∀ j x, x ∈ signedTubeDiamond ×ˢ Icc α β →
      (τ x ∈ S j ↔ x.1 ∈ signedTubeSheet j))
    (hfib : ∀ x ∈ signedTubeDiamond ×ˢ Icc α β,
      ∀ y ∈ signedTubeDiamond ×ˢ Icc α β,
      τ x = τ y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = α ∧ y.2 = β) ∨ (x.2 = β ∧ y.2 = α))) :
    ∃ σ : C3 → E,
      σ = τ ∘ periodicTubeCoordinates L d α β ∧
      FinitePiecewiseAffineOn σ (_root_.Dehn.identityTube L d) ∧
      σ '' _root_.Dehn.identityTube L d = τ '' (signedTubeDiamond ×ˢ Icc α β) ∧
      (∀ z ∈ _root_.Dehn.identityTube L d, ∀ w ∈ _root_.Dehn.identityTube L d,
        σ z = σ w ↔ z.1 = w.1 ∧ (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L))) ∧
      ∀ j z, z ∈ _root_.Dehn.identityTube L d →
        (σ z ∈ S j ↔ z.1.2 = if j = 0 then z.1.1 else -z.1.1) := by
  refine ⟨τ ∘ periodicTubeCoordinates L d α β, rfl,
    hτ.comp (periodicTubeCoordinates_finitePL hL hd α β)
      (periodicTubeCoordinates_mapsTo hL hd hab), ?_,
    normalized_identity_tube_fibers hL hd hab τ hfib, ?_⟩
  · rw [image_comp, periodicTubeCoordinates_image hL hd hab]
  · intro j z hz
    exact (hsheet j _ (periodicTubeCoordinates_mapsTo hL hd hab hz)).trans
      (periodicTubeCoordinates_sheet hL hd hab j z hz)

end PoincareConjecture.M76.Dehn
