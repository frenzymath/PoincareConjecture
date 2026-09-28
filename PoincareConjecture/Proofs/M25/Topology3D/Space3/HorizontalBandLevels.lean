import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalBandTracks












set_option autoImplicit false

open Set
open scoped ContDiff InnerProductSpace NNReal

namespace PoincareConjecture.M25.Topology3D

variable (u : UnitTwoSphere) (F : E3 → E3) {KF LF KV LV : ℝ≥0}
variable (hKF : LipschitzWith KF F) (hLF : ∀ y, ‖F y‖ ≤ LF)
variable (hKV : LipschitzWith KV (clockField (horizontalBandField u F)))
variable (hLV : ∀ p, ‖clockField (horizontalBandField u F) p‖ ≤ LV)
variable (β : ℝ → ℝ) {Kβ Lβ : ℝ≥0}
variable (hβK : LipschitzWith Kβ β) (hβL : ∀ z, ‖β z‖ ≤ Lβ)
variable {S : Set E3}
variable (hFβ : ∀ y ∈ S, ⟪(u : E3), F y⟫_ℝ = β ⟪(u : E3), y⟫_ℝ)
variable (hS : ∀ y ∈ S, ∀ t, boundedFlow F hKF hLF y t ∈ S)
variable (m : ℝ) {d : ℝ} (hd : 0 < d)
variable (hβ : ∀ z ∈ Ioo (m - d) (m + d), β z = 1)

include hβK hβL hFβ hS hd hβ



theorem horizontalBand_level_image {z : ℝ} (hz : z ∈ Ioo (m - d) (m + d)) :
    clockEvolution (horizontalBandField u F) hKV hLV m z ''
      {p : E2 | horizontalBandLift u (m, p) ∈ S} =
        {p : E2 | horizontalBandLift u (z, p) ∈ S} := by
  ext p
  constructor
  · rintro ⟨p, hp, rfl⟩
    have ht := (horizontalBand_regular_tracks u F hKF hLF hKV hLV β hβK hβL
      hFβ hS m hd hβ hp (horizontalBandLift_height u m p)).2 hz
    simp only [horizontalBandProjection_lift] at ht
    change horizontalBandLift u
      (z, clockEvolution (horizontalBandField u F) hKV hLV m z p) ∈ S
    rw [ht]
    exact hS _ hp _
  · intro hp
    let y := horizontalBandLift u (z, p)
    let x := boundedFlow F hKF hLF y (m - z)
    have hy : y ∈ S := hp
    have hyH : ⟪(u : E3), y⟫_ℝ = z := horizontalBandLift_height u z p
    have hx : x ∈ S := hS y hy (m - z)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    have hHb : ∀ w ∈ S, fderiv ℝ H w (F w) = β (H w) := by
      intro w hw
      simpa only [H.fderiv, H, InnerProductSpace.toDual_apply_apply] using hFβ w hw
    have hxH : ⟪(u : E3), x⟫_ℝ = m := by
      have ht := regularFlow_back_height F hKF hLF β hβK hβL H
        (fun _ _ => H.differentiableAt) hHb hS m hd hβ hy
          (show H y ∈ Ioo (m - d) (m + d) by
            simpa only [H, InnerProductSpace.toDual_apply_apply, hyH] using hz)
      simpa only [H, InnerProductSpace.toDual_apply_apply, hyH] using ht
    have hreturn : boundedFlow F hKF hLF x (z - m) = y := by
      dsimp [x]
      rw [← boundedFlow_add, show m - z + (z - m) = 0 by ring, boundedFlow_zero]
    have ht := (horizontalBand_regular_tracks u F hKF hLF hKV hLV β hβK hβL
      hFβ hS m hd hβ hx hxH).2 hz
    dsimp only at ht
    rw [hreturn] at ht
    refine ⟨horizontalBandProjection u x, ?_, ?_⟩
    · change horizontalBandLift u (m, horizontalBandProjection u x) ∈ S
      rwa [horizontalBandLift_reconstruct u x m hxH]
    · have heq := congrArg (horizontalBandProjection u) ht
      simpa only [y, horizontalBandProjection_lift] using heq



theorem horizontalBand_lift_mem_iff {z : ℝ} (hz : z ∈ Ioo (m - d) (m + d)) (p : E2) :
    horizontalBandLift u
        (z, clockEvolution (horizontalBandField u F) hKV hLV m z p) ∈ S ↔
      horizontalBandLift u (m, p) ∈ S := by
  have hi := horizontalBand_level_image u F hKF hLF hKV hLV β hβK hβL
    hFβ hS m hd hβ hz
  change clockEvolution (horizontalBandField u F) hKV hLV m z p ∈
      {q : E2 | horizontalBandLift u (z, q) ∈ S} ↔ _
  rw [← hi]
  exact (clockEvolutionEquiv (horizontalBandField u F) hKV hLV m z).injective.mem_set_image

end PoincareConjecture.M25.Topology3D
