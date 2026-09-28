import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalBandField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularLevelFlow













set_option autoImplicit false

open Set
open scoped ContDiff InnerProductSpace NNReal

namespace PoincareConjecture.M25.Topology3D

variable (u : UnitTwoSphere) (F : E3 → E3) {KF LF KV LV : ℝ≥0}
variable (hKF : LipschitzWith KF F) (hLF : ∀ y, ‖F y‖ ≤ LF)



theorem horizontalBandFlow_hasDerivAt (m : ℝ) (y : E3) (z : ℝ)
    (hz : ⟪(u : E3), boundedFlow F hKF hLF y (z - m)⟫_ℝ = z) :
    HasDerivAt (fun t => horizontalBandProjection u (boundedFlow F hKF hLF y (t - m)))
      (horizontalBandField u F
        (z, horizontalBandProjection u (boundedFlow F hKF hLF y (z - m)))) z := by
  have hd : HasDerivAt (fun t => boundedFlow F hKF hLF y (t - m))
      (F (boundedFlow F hKF hLF y (z - m))) z := by
    simpa only [Function.comp_def, id_eq, one_smul] using
      (boundedFlow_hasDerivAt F hKF hLF y (z - m)).scomp z
        ((hasDerivAt_id z).sub_const m)
  change HasDerivAt _ (horizontalBandProjection u
    (F (horizontalBandLift u
      (z, horizontalBandProjection u (boundedFlow F hKF hLF y (z - m)))))) z
  rw [horizontalBandLift_reconstruct u _ z hz]
  exact (horizontalBandProjection u).hasFDerivAt.comp_hasDerivAt z hd

variable (hKV : LipschitzWith KV (clockField (horizontalBandField u F)))
variable (hLV : ∀ p, ‖clockField (horizontalBandField u F) p‖ ≤ LV)



theorem horizontalBand_clockEvolution_tracks (y : E3) {a b m : ℝ}
    (hm : m ∈ Ioo a b)
    (hheight : ∀ z ∈ Ioo a b,
      ⟪(u : E3), boundedFlow F hKF hLF y (z - m)⟫_ℝ = z) :
    EqOn (fun z => clockEvolution (horizontalBandField u F) hKV hLV m z
      (horizontalBandProjection u y))
      (fun z => horizontalBandProjection u (boundedFlow F hKF hLF y (z - m)))
      (Ioo a b) := by
  have heq := clockEvolution_tracks (horizontalBandField u F) hKV hLV
    (fun z => horizontalBandProjection u (boundedFlow F hKF hLF y (z - m))) hm
    (fun z hz => horizontalBandFlow_hasDerivAt u F hKF hLF m y z (hheight z hz))
  simpa only [sub_self, boundedFlow_zero] using heq



theorem horizontalBand_clockEvolution_lift_tracks (y : E3) {a b m : ℝ}
    (hm : m ∈ Ioo a b)
    (hheight : ∀ z ∈ Ioo a b,
      ⟪(u : E3), boundedFlow F hKF hLF y (z - m)⟫_ℝ = z) :
    EqOn (fun z => horizontalBandLift u
      (z, clockEvolution (horizontalBandField u F) hKV hLV m z
        (horizontalBandProjection u y)))
      (fun z => boundedFlow F hKF hLF y (z - m)) (Ioo a b) := by
  intro z hz
  have ht := horizontalBand_clockEvolution_tracks u F hKF hLF hKV hLV y hm hheight hz
  dsimp only at ht ⊢
  rw [ht]
  exact horizontalBandLift_reconstruct u _ z (hheight z hz)

variable (β : ℝ → ℝ) {Kβ Lβ : ℝ≥0}
variable (hβK : LipschitzWith Kβ β) (hβL : ∀ z, ‖β z‖ ≤ Lβ)
variable {S : Set E3}
variable (hFβ : ∀ y ∈ S, ⟪(u : E3), F y⟫_ℝ = β ⟪(u : E3), y⟫_ℝ)
variable (hS : ∀ y ∈ S, ∀ t, boundedFlow F hKF hLF y t ∈ S)
variable (m : ℝ) {d : ℝ} (hd : 0 < d)
variable (hβ : ∀ z ∈ Ioo (m - d) (m + d), β z = 1)

include hβK hβL hFβ hS hd hβ



theorem horizontalBandFlow_regular_height {y : E3} (hy : y ∈ S)
    (hym : ⟪(u : E3), y⟫_ℝ = m) {z : ℝ} (hz : z ∈ Ioo (m - d) (m + d)) :
    ⟪(u : E3), boundedFlow F hKF hLF y (z - m)⟫_ℝ = z := by
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  have hHb : ∀ x ∈ S, fderiv ℝ H x (F x) = β (H x) := by
    intro x hx
    simpa only [H.fderiv, H, InnerProductSpace.toDual_apply_apply] using hFβ x hx
  have ht : z - m ∈ Ioo (-d) d := ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have heq := regularFlow_height F hKF hLF β hβK hβL H
    (fun x _ => H.differentiableAt) hHb hS m hd hβ hy hym ht
  exact heq.trans (by ring)



theorem horizontalBand_regular_tracks {y : E3} (hy : y ∈ S)
    (hym : ⟪(u : E3), y⟫_ℝ = m) :
    EqOn (fun z => clockEvolution (horizontalBandField u F) hKV hLV m z
      (horizontalBandProjection u y))
      (fun z => horizontalBandProjection u (boundedFlow F hKF hLF y (z - m)))
      (Ioo (m - d) (m + d)) ∧
    EqOn (fun z => horizontalBandLift u
      (z, clockEvolution (horizontalBandField u F) hKV hLV m z
        (horizontalBandProjection u y)))
      (fun z => boundedFlow F hKF hLF y (z - m)) (Ioo (m - d) (m + d)) := by
  have hm : m ∈ Ioo (m - d) (m + d) := ⟨by linarith, by linarith⟩
  have hheight : ∀ z ∈ Ioo (m - d) (m + d),
      ⟪(u : E3), boundedFlow F hKF hLF y (z - m)⟫_ℝ = z :=
    fun _ hz => horizontalBandFlow_regular_height u F hKF hLF β hβK hβL
      hFβ hS m hd hβ hy hym hz
  exact ⟨horizontalBand_clockEvolution_tracks u F hKF hLF hKV hLV y hm hheight,
    horizontalBand_clockEvolution_lift_tracks u F hKF hLF hKV hLV y hm hheight⟩

end PoincareConjecture.M25.Topology3D
