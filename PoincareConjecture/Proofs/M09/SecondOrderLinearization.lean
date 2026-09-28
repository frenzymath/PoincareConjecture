import PoincareConjecture.Proofs.M09.SmoothPartials
import PoincareConjecture.Proofs.M09.LinearizedODE








set_option autoImplicit false

open scoped ContDiff Topology
open Filter

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_variation_phase_of_ode (f : ℝ × ℝ → E) (B : ℝ × (E × E) → E × E)
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (s : ℝ) (hs : (s, 0) ∈ U)
    (hB : DifferentiableAt ℝ B (s, timeDerivativePhase f (s, 0)))
    (hode : ∀ᶠ u in 𝓝 (0 : ℝ), HasDerivAt (fun r ↦ timeDerivativePhase f (r, u))
      (B (s, timeDerivativePhase f (s, u))) s) :
    let Y : ℝ → E := fun r ↦ deriv (fun u ↦ f (r, u)) 0
    HasDerivAt (fun r ↦ (Y r, deriv Y r))
      (fderiv ℝ B (s, timeDerivativePhase f (s, 0)) (0, (Y s, deriv Y s))) s := by
  let Y : ℝ → E := fun r ↦ deriv (fun u ↦ f (r, u)) 0
  have hlin := hasDerivAt_variation_of_ode (timeDerivativePhase f) B s
    ((timeDerivativePhase_contDiffOn f U hU hf).contDiffAt (hU.mem_nhds hs)) hB hode
  have heq : (fun r ↦ deriv (fun u ↦ timeDerivativePhase f (r, u)) 0) =ᶠ[𝓝 s]
      (fun r ↦ (Y r, deriv Y r)) := by
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (hU.mem_nhds hs)] with r hr
    exact deriv_timeDerivativePhase_variation f U hU hf r hr
  rw [heq.eq_of_nhds] at hlin
  exact hlin.congr_of_eventuallyEq heq.symm

end PoincareConjecture.Proofs.M09
