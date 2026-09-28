import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BoundedHeightTracks
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalBandTracks











set_option autoImplicit false

open Set Metric
open scoped InnerProductSpace NNReal

namespace PoincareConjecture.M25.Topology3D

variable (u : UnitTwoSphere) (F : E3 → E3) {KF LF KV LV : ℝ≥0}
variable (hKF : LipschitzWith KF F) (hLF : ∀ y, ‖F y‖ ≤ LF)
variable (hKV : LipschitzWith KV (clockField (horizontalBandField u F)))
variable (hLV : ∀ p, ‖clockField (horizontalBandField u F) p‖ ≤ LV)

local notation "Phi" => boundedFlow F hKF hLF
local notation "H" => InnerProductSpace.toDual ℝ E3 (u : E3)
local notation "P" => horizontalBandProjection u
local notation "lft" => horizontalBandLift u
local notation "Xi" => clockEvolution (horizontalBandField u F) hKV hLV



theorem horizontalBand_clockEvolution_mem_iff_of_height_tracks
    {S A : Set E3} {τ c z : ℝ} (hτ : 0 < τ)
    (hS : ∀ y ∈ S, ∀ t : ℝ, Phi y t ∈ S)
    (hheight : ∀ y ∈ A, ∀ t : ℝ, |t| ≤ τ → H (Phi y t) = H y + t)
    (x : E2) (hcz : |z - c| < τ)
    (hstart : lft (c, x) ∈ S → lft (c, x) ∈ A)
    (hfinish : lft (z, Xi c z x) ∈ S → lft (z, Xi c z x) ∈ A) :
    lft (z, Xi c z x) ∈ S ↔ lft (c, x) ∈ S := by
  have htrack (m : ℝ) (v : E2) (hy : lft (m, v) ∈ A) :
      EqOn (fun r => lft (r, Xi m r v))
        (fun r => Phi (lft (m, v)) (r - m)) (Ioo (m - τ) (m + τ)) := by
    have hm : m ∈ Ioo (m - τ) (m + τ) := ⟨by linarith, by linarith⟩
    have hh (r : ℝ) (hr : r ∈ Ioo (m - τ) (m + τ)) :
        ⟪(u : E3), Phi (lft (m, v)) (r - m)⟫_ℝ = r := by
      have ht : |r - m| ≤ τ := abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
      have heq := hheight (lft (m, v)) hy (r - m) ht
      simp only [InnerProductSpace.toDual_apply_apply, horizontalBandLift_height] at heq
      linarith
    simpa only [horizontalBandProjection_lift] using
      horizontalBand_clockEvolution_lift_tracks u F hKF hLF hKV hLV (lft (m, v)) hm hh
  constructor
  · intro hy
    have hc : c ∈ Ioo (z - τ) (z + τ) := by
      obtain ⟨hl, hr⟩ := abs_lt.mp hcz
      exact ⟨by linarith, by linarith⟩
    have heq := htrack z (Xi c z x) (hfinish hy) hc
    simp only [clockEvolution_reverse] at heq
    rw [heq]
    exact hS _ hy _
  · intro hy
    have hz : z ∈ Ioo (c - τ) (c + τ) := by
      obtain ⟨hl, hr⟩ := abs_lt.mp hcz
      exact ⟨by linarith, by linarith⟩
    have heq : lft (z, Xi c z x) = Phi (lft (c, x)) (z - c) :=
      htrack c x (hstart hy) hz
    rw [heq]
    exact hS _ hy _



theorem horizontalBand_clockEvolution_mem_iff_of_margin
    {S A : Set E3} {N W : Set E2} {τ c b ε δ : ℝ}
    (hε : 0 < ε) (hετ : ε < τ) (hεb : ε ≤ b) (hδ : 0 < δ)
    (hgap : Metric.thickening δ N ⊆ W) (hmove : (LV : ℝ) * ε < δ)
    (hS : ∀ y ∈ S, ∀ t : ℝ, Phi y t ∈ S)
    (hheight : ∀ y ∈ A, ∀ t : ℝ, |t| ≤ τ → H (Phi y t) = H y + t)
    (hsafe : ∀ y ∈ S, |H y - c| ≤ b → P y ∉ N → y ∈ A)
    (x : E2) (hx : x ∉ W) (z : ℝ) (hz : |z - c| ≤ ε) :
    lft (z, Xi c z x) ∈ S ↔ lft (c, x) ∈ S := by
  have hxN : x ∉ N := fun hn => hx (hgap (self_subset_thickening hδ N hn))
  have hdist : dist (Xi c z x) x < δ := by
    rw [dist_eq_norm]
    exact (clockEvolution_norm_sub_le (horizontalBandField u F) hKV hLV c z x).trans_lt
      ((mul_le_mul_of_nonneg_left hz LV.coe_nonneg).trans_lt hmove)
  have hvN : Xi c z x ∉ N := by
    intro hn
    exact hx (hgap (mem_thickening_iff.mpr ⟨Xi c z x, hn, by rwa [dist_comm]⟩))
  apply horizontalBand_clockEvolution_mem_iff_of_height_tracks u F hKF hLF hKV hLV
    (hε.trans hετ) hS hheight x (hz.trans_lt hετ)
  · intro hy
    apply hsafe _ hy
    · simpa only [InnerProductSpace.toDual_apply_apply, horizontalBandLift_height,
        sub_self, abs_zero] using hε.le.trans hεb
    · simpa only [horizontalBandProjection_lift] using hxN
  · intro hy
    apply hsafe _ hy
    · simpa only [InnerProductSpace.toDual_apply_apply, horizontalBandLift_height] using
        hz.trans hεb
    · simpa only [horizontalBandProjection_lift] using hvN

end PoincareConjecture.M25.Topology3D
