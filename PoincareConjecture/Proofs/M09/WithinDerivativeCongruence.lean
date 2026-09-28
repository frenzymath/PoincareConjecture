import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Deriv








set_option autoImplicit false

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem deriv_eq_of_eqOn {f g : ℝ → E} {K : Set ℝ} {s : ℝ}
    (heq : Set.EqOn f g K) (hs : s ∈ K) (hK : UniqueDiffWithinAt ℝ K s)
    (hf : DifferentiableAt ℝ f s) (hg : DifferentiableAt ℝ g s) :
    deriv f s = deriv g s := by
  rw [← hf.derivWithin hK, ← hg.derivWithin hK]
  exact derivWithin_congr heq (heq hs)

theorem hasDerivAt_congr_of_eqOn {f g : ℝ → E} {K : Set ℝ} {s : ℝ} {v : E}
    (heq : Set.EqOn f g K) (hs : s ∈ K) (hK : UniqueDiffWithinAt ℝ K s)
    (hf : HasDerivAt f v s) (hg : DifferentiableAt ℝ g s) :
    HasDerivAt g v s :=
  hg.hasDerivAt.congr_deriv
    ((deriv_eq_of_eqOn heq hs hK hf.differentiableAt hg).symm.trans hf.deriv)

theorem hasDerivAt_phase_congr_of_eqOn {f g : ℝ → E} {K : Set ℝ} {s : ℝ} {v : E × E}
    (heq : Set.EqOn f g K) (hs : s ∈ K) (hK : UniqueDiffOn ℝ K)
    (hf : ∀ r ∈ K, DifferentiableAt ℝ f r)
    (hg : ∀ r ∈ K, DifferentiableAt ℝ g r)
    (hdg : DifferentiableAt ℝ (deriv g) s)
    (hphase : HasDerivAt (fun r ↦ (f r, deriv f r)) v s) :
    HasDerivAt (fun r ↦ (g r, deriv g r)) v s := by
  apply hasDerivAt_congr_of_eqOn (K := K) (s := s) ?_ hs (hK s hs) hphase
    ((hg s hs).prodMk hdg)
  intro r hr
  exact Prod.ext (heq hr) (deriv_eq_of_eqOn heq hr (hK r hr) (hf r hr) (hg r hr))

end PoincareConjecture.Proofs.M09
