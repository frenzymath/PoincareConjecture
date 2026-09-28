import PoincareConjecture.Proofs.M09.MeetingMomentumDerivative

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem positiveMomentum_deriv_eq_zero
    (a ξ : ℝ → E) (G : E → E →L[ℝ] E →L[ℝ] ℝ) (S : E → ℝ)
    (ha : ContDiffAt ℝ ∞ a 0) (hξ : ContDiffAt ℝ ∞ ξ 0)
    (hG : ContDiffAt ℝ ∞ G (a 0)) (hS : ContDiffAt ℝ ∞ S (a 0))
    (hpos : ∀ v : E, v ≠ 0 → 0 < G (a 0) v v)
    (ha0 : deriv a 0 = 0)
    (hR0 : deriv (fun r ↦ G (a r) (ξ r) + fderiv ℝ S (a r)) 0 = 0) :
    deriv ξ 0 = 0 := by
  have haD := (ha.differentiableAt (by simp)).hasDerivAt
  have hξD := (hξ.differentiableAt (by simp)).hasDerivAt
  have hGa : HasDerivAt (fun r ↦ G (a r)) 0 0 := by
    simpa only [Function.comp_def, ha0, map_zero] using
      (hG.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) haD
  have hDS : DifferentiableAt ℝ (fderiv ℝ S) (a 0) :=
    (hS.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hSa : HasDerivAt (fun r ↦ fderiv ℝ S (a r)) 0 0 := by
    simpa only [Function.comp_def, ha0, map_zero] using
      hDS.hasFDerivAt.comp_hasDerivAt (0 : ℝ) haD
  have hRP : HasDerivAt (fun r ↦ G (a r) (ξ r) + fderiv ℝ S (a r))
      (G (a 0) (deriv ξ 0)) 0 := by
    convert! (hGa.clm_apply hξD).add hSa using 1 <;>
      simp only [ContinuousLinearMap.zero_apply, zero_add, add_zero, Pi.add_def]
  have hzero : G (a 0) (deriv ξ 0) = 0 := hRP.deriv.symm.trans hR0
  by_contra hne
  have hdiag : G (a 0) (deriv ξ 0) (deriv ξ 0) = 0 :=
    congrArg (fun L : E →L[ℝ] ℝ ↦ L (deriv ξ 0)) hzero
  exact (hpos (deriv ξ 0) hne).ne' hdiag

end PoincareConjecture.Proofs.M09
