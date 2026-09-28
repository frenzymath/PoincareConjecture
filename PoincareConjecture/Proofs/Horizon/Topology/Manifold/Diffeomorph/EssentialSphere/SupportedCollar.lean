import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.RadialCollar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Puncture.Extension










set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare

open PoincareConjecture

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)



theorem exists_ambient_extension_of_outward_sphere_collar
    (c : OpenPartialHomeomorph RoundCylinderSpace E3)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ)
    (hsource : (univ : Set UnitTwoSphere) ×ˢ Ioo (-δ) δ ⊆ c.source)
    (hzero : ∀ q : UnitTwoSphere, c (q, 0) = (q : E3))
    (hpositive : ∀ (q : UnitTwoSphere) (t : ℝ), 0 < t → t < δ → 1 < ‖c (q, t)‖)
    (R : ℝ) (hR : 0 < R) :
    ∃ (η : ℝ) (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
      0 < η ∧ η < δ ∧ η < R ∧
      F '' closedBall 0 1 = closedBall 0 1 ∧
      (∀ p : RoundCylinderSpace, |p.2| < η →
        F (Real.exp p.2 • (p.1 : E3)) = c p) ∧
      (∀ x : E3, ‖x‖ ≤ Real.exp (-R) ∨ Real.exp R ≤ ‖x‖ → F x = x) := by
  obtain ⟨η, D, hη, hηδ, hηR, hagree, hout⟩ :=
    exists_supported_radial_collar_transition c hc hci hδ hsource hzero hpositive R hR
  have hDzero (q : UnitTwoSphere) : D (q, 0) = (q, 0) := by
    apply sphereCylinderDiffeomorphPunctured.injective
    apply Subtype.ext
    simpa [sphereCylinderDiffeomorphPunctured_apply, hzero] using
      hagree (q, 0) (by simpa using hη)
  obtain ⟨F, hball, hF, hsmall⟩ :=
    exists_ball_preserving_extension_of_cylinder_negative_tail D R
      (fun p hp => hout p (by have := neg_le_abs p.2; linarith)) hDzero
  have hcollar (p : RoundCylinderSpace) (hp : |p.2| < η) :
      F (Real.exp p.2 • (p.1 : E3)) = c p := (hF p).trans (hagree p hp)
  have hfix (x : E3) (hx : ‖x‖ ≤ Real.exp (-R) ∨ Real.exp R ≤ ‖x‖) : F x = x := by
    by_cases hx0 : x = 0
    · subst x
      exact hsmall 0 (by simpa using Real.exp_pos (-R))
    · let p := sphereCylinderDiffeomorphPunctured.symm ⟨x, hx0⟩
      have hp : Real.exp p.2 • (p.1 : E3) = x :=
        congrArg Subtype.val (sphereCylinderDiffeomorphPunctured.apply_symm_apply ⟨x, hx0⟩)
      have hnorm : ‖x‖ = Real.exp p.2 := by
        rw [← hp, norm_smul]
        simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hbound : R ≤ |p.2| := by
        rw [hnorm] at hx
        rcases hx with hx | hx
        · have := Real.exp_le_exp.mp hx
          have := neg_le_abs p.2
          linarith
        · exact (Real.exp_le_exp.mp hx).trans (le_abs_self p.2)
      calc
        F x = F (Real.exp p.2 • (p.1 : E3)) := congrArg F hp.symm
        _ = Real.exp (D p).2 • ((D p).1 : E3) := hF p
        _ = x := by rw [hout p hbound]; exact hp
  exact ⟨η, F, hη, hηδ, hηR, hball, hcollar, hfix⟩

end Poincare
