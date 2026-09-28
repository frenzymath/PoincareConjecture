import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem shiftedCost_fderiv (L : ℝ × E → ℝ) (S : E → ℝ) (a : ℝ → E)
    (P : E →L[ℝ] ℝ) (r : ℝ)
    (hL : DifferentiableAt ℝ L (r, a r)) (hS : DifferentiableAt ℝ S (a r))
    (ha : DifferentiableAt ℝ a r)
    (hprefix : ∀ w : ℝ × E, fderiv ℝ L (r, a r) w = P w.2) (w : ℝ × E) :
    fderiv ℝ (fun z : ℝ × E ↦ L (z.1, a z.1 + z.2) + S (a z.1 + z.2)) (r, 0) w =
      (P + fderiv ℝ S (a r)) (fderiv ℝ a r w.1 + w.2) := by
  have hy : HasFDerivAt (fun z : ℝ × E ↦ a z.1 + z.2)
      ((fderiv ℝ a r).comp (ContinuousLinearMap.fst ℝ ℝ E) + ContinuousLinearMap.snd ℝ ℝ E)
      (r, 0) := (ha.hasFDerivAt.comp (r, (0 : E)) hasFDerivAt_fst).add hasFDerivAt_snd
  have hL' : DifferentiableAt ℝ L (r, a r + 0) := by simpa only [add_zero] using hL
  have hS' : DifferentiableAt ℝ S (a r + 0) := by simpa only [add_zero] using hS
  have hcost := (hL'.hasFDerivAt.comp (r, (0 : E)) (hasFDerivAt_fst.prodMk hy)).add
    (hS'.hasFDerivAt.comp (r, (0 : E)) hy)
  have heval : fderiv ℝ (fun z : ℝ × E ↦ L (z.1, a z.1 + z.2) + S (a z.1 + z.2)) (r, 0) w =
      fderiv ℝ L (r, a r) (w.1, fderiv ℝ a r w.1 + w.2) +
        fderiv ℝ S (a r) (fderiv ℝ a r w.1 + w.2) := by
    simpa only [Function.comp_def, Pi.add_def, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      add_zero] using congrArg (fun B : (ℝ × E) →L[ℝ] ℝ ↦ B w) hcost.fderiv
  rw [heval, hprefix]
  rfl

end PoincareConjecture.Proofs.M09
