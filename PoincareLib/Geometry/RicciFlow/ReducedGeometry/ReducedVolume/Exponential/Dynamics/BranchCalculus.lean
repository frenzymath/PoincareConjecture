import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Exponential.Dynamics.PhaseField
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Exponential.Dynamics.MixedAction
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Exponential.Coordinates.ProductDerivatives

/-!
# The phase equation of a smooth action branch

The actual endpoint velocity defines its covector momentum. The two action
identities imply its momentum equation by symmetry of second derivatives.
All three components therefore solve the same autonomous phase equation.
-/

set_option autoImplicit false

open Filter
open scoped ContDiff Topology

namespace PoincareMT.ReducedVolume

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- Covector momentum of the actual endpoint-time branch. -/
noncomputable def actionBranchMomentum (E : X × ℝ → Y)
    (B : Y × ℝ → Y →L[ℝ] Y →L[ℝ] ℝ) (z : X × ℝ) : Y →L[ℝ] ℝ :=
  (2 * Real.sqrt z.2) • B (E z, z.2) (fderiv ℝ E z (0, 1))

/-- The time, endpoint, and momentum of one fixed initial vector. -/
noncomputable def actionBranchPhase (E : X × ℝ → Y)
    (B : Y × ℝ → Y →L[ℝ] Y →L[ℝ] ℝ) (Z : X) (t : ℝ) :
    ℝ × Y × (Y →L[ℝ] ℝ) :=
  (t, E (Z, t), actionBranchMomentum E B (Z, t))

/-- Smooth endpoint and metric germs give a smooth actual momentum at positive time. -/
theorem actionBranchMomentum_contDiffAt {E : X × ℝ → Y}
    {B : Y × ℝ → Y →L[ℝ] Y →L[ℝ] ℝ} {z : X × ℝ}
    (hE : ContDiffAt ℝ ∞ E z) (hB : ContDiffAt ℝ ∞ B (E z, z.2))
    (ht : 0 < z.2) : ContDiffAt ℝ ∞ (actionBranchMomentum E B) z := by
  exact (contDiffAt_const.mul (contDiffAt_snd.sqrt ht.ne')).smul
    ((hB.comp z (hE.prodMk contDiffAt_snd)).clm_apply
      ((hE.fderiv_right (by simp)).clm_apply contDiffAt_const))

/-- The two actual action germs yield the full phase equation at a noncritical point. -/
theorem hasDerivAt_actionBranchPhase
    {E : X × ℝ → Y} {A : X × ℝ → ℝ}
    {B : Y × ℝ → Y →L[ℝ] Y →L[ℝ] ℝ} {R : Y × ℝ → ℝ} {z : X × ℝ}
    (hE : ContDiffAt ℝ 2 E z) (hA : ContDiffAt ℝ 2 A z)
    (hP : DifferentiableAt ℝ (actionBranchMomentum E B) z)
    (hL : DifferentiableAt ℝ (kineticLagrangian B R)
      (z.2, E z, fderiv ℝ E z (0, 1)))
    (ht : 0 < z.2) (hi : (B (E z, z.2)).IsInvertible)
    (hsym : ∀ u v : Y, B (E z, z.2) u v = B (E z, z.2) v u)
    (hspace : ∀ᶠ w in 𝓝 z, ∀ h : X,
      fderiv ℝ A w (h, 0) = actionBranchMomentum E B w (fderiv ℝ E w (h, 0)))
    (htime : ∀ᶠ w in 𝓝 z,
      fderiv ℝ A w (0, 1) = kineticLagrangian B R
        (w.2, E w, fderiv ℝ E w (0, 1)))
    (hsurj : Function.Surjective (fun h : X ↦ fderiv ℝ E z (h, 0))) :
    HasDerivAt (actionBranchPhase E B z.1)
      (phaseField B R (actionBranchPhase E B z.1 z.2)) z.2 := by
  have hvelocity (v : Y) :
      fderiv ℝ (kineticLagrangian B R) (z.2, E z, fderiv ℝ E z (0, 1))
        (0, 0, v) = actionBranchMomentum E B z v := by
    exact kineticLagrangian_velocity_derivative hL hsym v
  have hmoment : fderiv ℝ (actionBranchMomentum E B) z (0, 1) =
      (fderiv ℝ (kineticLagrangian B R) (z.2, E z, fderiv ℝ E z (0, 1))).comp
        ((0 : Y →L[ℝ] ℝ).prod
          ((ContinuousLinearMap.id ℝ Y).prod (0 : Y →L[ℝ] Y))) := by
    ext v
    exact momentum_time_derivative_of_action hE hA hP hL
      hspace htime hvelocity hsurj v
  have hd : HasDerivAt (actionBranchPhase E B z.1)
      (1, fderiv ℝ E z (0, 1), fderiv ℝ (actionBranchMomentum E B) z (0, 1)) z.2 :=
    (hasDerivAt_id z.2).prodMk
      ((hasDerivAt_time_slice (hE.differentiableAt two_ne_zero)).prodMk
        (hasDerivAt_time_slice hP))
  have heq : phaseField B R (actionBranchPhase E B z.1 z.2) =
      (1, fderiv ℝ E z (0, 1), fderiv ℝ (actionBranchMomentum E B) z (0, 1)) := by
    dsimp only [phaseField, actionBranchPhase, actionBranchMomentum]
    rw [phaseVelocity_of_momentum B (E z) ht hi, hmoment]
  rwa [← heq] at hd

end PoincareMT.ReducedVolume
