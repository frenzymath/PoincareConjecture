import PoincareConjecture.Proofs.M38.SphereTwoBallCylinder
import PoincareConjecture.Proofs.M38.UniformCylinderEnds
import PoincareConjecture.Proofs.M38.CylinderReparametrization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

noncomputable def sphereTwoBallEndCoefficient (a : UnitThreeSphere)
    (L : StandardCapSpace ≃L[ℝ] StandardCapSpace) (b r : ℝ) (w : UnitTwoSphere) : ℝ :=
  r * b * ‖L ((spherePoleDirection a L).symm w).val‖ / 4

theorem sphereTwoBallEndCoefficient_pos (a : UnitThreeSphere)
    (L : StandardCapSpace ≃L[ℝ] StandardCapSpace) {b r : ℝ}
    (hb : 0 < b) (hr : 0 < r) (w : UnitTwoSphere) :
    0 < sphereTwoBallEndCoefficient a L b r w := by
  exact div_pos (mul_pos (mul_pos hr hb)
    (norm_pos_iff.mpr (linearSphereVector_ne_zero L ((spherePoleDirection a L).symm w))))
      (by norm_num)

theorem sphereTwoBallEndCoefficient_smooth (a : UnitThreeSphere)
    (L : StandardCapSpace ≃L[ℝ] StandardCapSpace) (b r : ℝ) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (sphereTwoBallEndCoefficient a L b r) := by
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) :=
    ⟨by simp [StandardCapSpace]⟩
  have hL : ContMDiff (𝓡 2) (𝓡 3) ∞
      (fun w : UnitTwoSphere => L ((spherePoleDirection a L).symm w).val) :=
    L.contDiff.contMDiff.comp
      (contMDiff_coe_sphere.comp (spherePoleDirection a L).symm.contMDiff)
  have hnorm : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun w : UnitTwoSphere => ‖L ((spherePoleDirection a L).symm w).val‖) := by
    intro w
    exact (contDiffAt_norm ℝ
      (linearSphereVector_ne_zero L ((spherePoleDirection a L).symm w))).contMDiffAt.comp
        w hL.contMDiffAt
  exact ((contDiff_const.mul contDiff_id).div_const 4).contMDiff.comp hnorm

@[simp] theorem sphereTwoBallEndCoefficient_apply (a : UnitThreeSphere)
    (L : StandardCapSpace ≃L[ℝ] StandardCapSpace) (b r : ℝ) (z : UnitTwoSphere) :
    sphereTwoBallEndCoefficient a L b r (spherePoleDirection a L z) =
      r * b * ‖L z.val‖ / 4 := by
  unfold sphereTwoBallEndCoefficient
  rw [Diffeomorph.symm_apply_apply]

theorem exists_alignedSphereTwoBallCylinder
    (B₀ B₁ : SurgeryBallEmbedding sphereCarrier.{u})
    (hdisjoint : Disjoint (B₀.map '' Metric.ball 0 2) (B₁.map '' Metric.ball 0 2)) :
    ∃ C : OpenCylinderModel (B₀.closedBall ∪ B₁.closedBall)ᶜ,
    ∃ θ₀ θ₁ : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
    ∃ k η : ℝ, 0 < k ∧ k ≤ 1 / 2 ∧ 0 < η ∧ η ≤ 1 / 8 ∧
      (∀ z : UnitTwoSphere, ∀ s : ℝ, 0 < s → s < η →
        C.inverse (B₁.map ((1 + s) • z.val)) = (θ₁ z, k * s)) ∧
      (∀ z : UnitTwoSphere, ∀ s : ℝ, 0 < s → s < η →
        C.inverse (B₀.map ((1 + s) • z.val)) = (θ₀ z, 1 - k * s)) := by
  obtain ⟨C, a, L₀, L₁, b, r, ε, hb, hr, hε, hε4, hlower, hupper⟩ :=
    exists_sphereTwoBallCylinder B₀ B₁ hdisjoint
  let A := sphereTwoBallEndCoefficient a L₀ b r
  obtain ⟨G, k, η, hk, hk2, hη, hη8, hG, hangle, hGlow, hGup⟩ :=
    exists_cylinderEndReparametrization A (sphereTwoBallEndCoefficient_smooth a L₀ b r)
      (sphereTwoBallEndCoefficient_pos a L₀ hb hr)
  refine ⟨reparametrizeCylinder G hG C, spherePoleDirection a L₀,
    linearSphereDiffeomorph L₁, k, min ε η, hk, hk2, lt_min hε hη,
      (min_le_right _ _).trans hη8, ?_, ?_⟩
  · intro z s hs hsη
    have hsε : s < ε := hsη.trans_le (min_le_left _ _)
    have hsη' : s < η := hsη.trans_le (min_le_right _ _)
    have hrational : 1 - 1 / (1 + s) = s / (1 + s) := by
      field_simp [show 1 + s ≠ 0 by linarith]
      ring
    rw [reparametrizeCylinder_inverse, hlower z (1 + s) (by linarith) (by linarith),
      hrational]
    exact hGlow (linearSphereDiffeomorph L₁ z) s hs hsη'
  · intro z s hs hsη
    have hsε : s < ε := hsη.trans_le (min_le_left _ _)
    have hsη' : s < η := hsη.trans_le (min_le_right _ _)
    have hcoefficient : r * b * punctureRadialOrderIso (1 + s) * ‖L₀ z.val‖ / 4 =
        A (spherePoleDirection a L₀ z) * punctureRadialOrderIso (1 + s) := by
      dsimp only [A]
      rw [sphereTwoBallEndCoefficient_apply]
      ring
    rw [reparametrizeCylinder_inverse, hupper z (1 + s) (by linarith) (by linarith),
      hcoefficient]
    exact hGup (spherePoleDirection a L₀ z) s hs hsη'

end PoincareConjecture.M38
