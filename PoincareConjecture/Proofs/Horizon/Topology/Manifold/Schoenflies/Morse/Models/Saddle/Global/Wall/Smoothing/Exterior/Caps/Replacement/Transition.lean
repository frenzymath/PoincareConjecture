import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.Profile
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.Radial

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps

open Split

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private abbrev axis : E3 := EuclideanSpace.single 2 1

theorem tangentPlanarLatitude_normalized_horizontal (p : E3)
    (hp : p 2 ∈ Ioo (-1 : Real) 1) :
    tangentPlanarLatitude (p 2) ((Real.sqrt (1 - p 2 ^ 2))⁻¹ • horizontal p) = p := by
  have hr : Real.sqrt (1 - p 2 ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr (sphereLatitude_radicand_pos hp)).ne'
  ext i
  fin_cases i
  · change Real.sqrt (1 - p 2 ^ 2) * ((Real.sqrt (1 - p 2 ^ 2))⁻¹ * p 0) = p 0
    rw [← mul_assoc, mul_inv_cancel₀ hr, one_mul]
  · change Real.sqrt (1 - p 2 ^ 2) * ((Real.sqrt (1 - p 2 ^ 2))⁻¹ * p 1) = p 1
    rw [← mul_assoc, mul_inv_cancel₀ hr, one_mul]
  · rfl

theorem exists_profile_cap_transition_with_equatorial_formula {ρ : Real → Real}
    (hρ : ContDiff Real ∞ ρ) (H : Real ≃ₘ[Real] Real) (a R : Real)
    {δ : Real} (hδ : 0 ≤ δ) :
    ∃ G E : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ p, G p 2 = p 2) ∧
      E '' (planarCapLift (profilePlanarDiffeomorph hρ H a R 0
        (by constructor <;> norm_num)) '' boundedCylinderNorthernCap axis) =
          G '' (sphere (0 : E3) 1 ∩ {p | 0 ≤ p 2}) ∧
      (∀ s ∈ Icc (-δ) δ, ∀ p : S2, |Real.exp s * (p : E3) 2| ≤ 1 / 16 →
        E (planarCapLift (profilePlanarDiffeomorph hρ H a R 0
          (by constructor <;> norm_num))
            (boundedCylinderRadius axis p • (Real.exp s • (p : E3)))) =
              sliceAtHeight (Real.exp s * (p : E3) 2)
                (profilePlanarDiffeomorph hρ H a R 0 (by constructor <;> norm_num)
                  ((Real.sqrt (1 - (Real.exp s * (p : E3) 2) ^ 2))⁻¹ •
                    horizontal (Real.exp s • (p : E3))))) ∧
      (∀ s ∈ Icc (-δ) δ, ∀ p : S2, (p : E3) 2 = 0 →
        E (planarCapLift (profilePlanarDiffeomorph hρ H a R 0
          (by constructor <;> norm_num)) (Real.exp s • (p : E3))) =
            planarCapLift (profilePlanarDiffeomorph hρ H a R 0
              (by constructor <;> norm_num)) (Real.exp s • (p : E3))) := by
  obtain ⟨G, hGheight, hGlocal, _, _⟩ := exists_profile_cap_with_canonical_collar hρ H a R
  obtain ⟨C, _, hC, _, hCcap⟩ := exists_boundedCylinder_ambient_with_annular_formula axis hδ
  let A := profilePlanarDiffeomorph hρ H a R 0 (by constructor <;> norm_num)
  let L := planarCapLift A
  let E := (L.symm.trans C.symm).trans G
  have hE (x : E3) : E (L (C x)) = G x := by
    change G (C.symm (L.symm (L (C x)))) = G x
    rw [L.symm_apply_apply, C.symm_apply_apply]
  have hGformula (x : E3) (hx : |x 2| ≤ 1 / 16) :
      G x = sliceAtHeight (x 2) (A ((Real.sqrt (1 - x 2 ^ 2))⁻¹ • horizontal x)) := by
    have hxI : x 2 ∈ Ioo (-1 : Real) 1 := by
      obtain ⟨hl, hu⟩ := abs_le.mp hx
      constructor <;> linarith
    exact (congrArg G (tangentPlanarLatitude_normalized_horizontal x hxI)).symm.trans
      (hGlocal _ hx _)
  have hcap : C '' (sphere (0 : E3) 1 ∩ {p | 0 ≤ p 2}) =
      boundedCylinderNorthernCap axis := by
    simpa [axis, EuclideanSpace.inner_single_left] using hCcap
  refine ⟨G, E, hGheight, ?_, ?_, ?_⟩
  · change E '' (L '' boundedCylinderNorthernCap axis) = _
    rw [← hcap, image_image, image_image]
    exact image_congr (fun x _ => hE x)
  · intro s hs p hp
    change E (L (boundedCylinderRadius axis p • (Real.exp s • (p : E3)))) = _
    rw [← hC s hs p, hE]
    exact hGformula (Real.exp s • (p : E3)) hp
  · intro s hs p hp
    have hr : boundedCylinderRadius axis p = 1 := by
      have hpi : inner Real axis (p : E3) = 0 := by
        simpa [axis, EuclideanSpace.inner_single_left] using hp
      rw [boundedCylinderRadius_of_abs_height_le axis p (by rw [hpi]; norm_num), hpi]
      norm_num
    have hCx : C (Real.exp s • (p : E3)) = Real.exp s • (p : E3) := by
      rw [hC s hs p, hr, one_smul]
    have hx : (Real.exp s • (p : E3)) 2 = 0 := by simp [hp]
    change E (L (Real.exp s • (p : E3))) = L (Real.exp s • (p : E3))
    rw [← hCx, hE, hCx]
    rw [hGformula _ (by rw [hx]; norm_num), hx, planarCapLift_apply, hx]
    norm_num

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps
