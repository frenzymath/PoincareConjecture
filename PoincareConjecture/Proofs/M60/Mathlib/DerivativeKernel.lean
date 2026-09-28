import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp

set_option autoImplicit false

open Filter Asymptotics
open scoped Topology

namespace PoincareConjecture.M60

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem hasDerivAt_zero_of_increment_bound {f : ℝ → F} {g : ℝ → G}
    {x C : ℝ} (hf : HasDerivAt f 0 x)
    (hbound : ∀ᶠ y in 𝓝 x, ‖g y - g x‖ ≤ C * ‖f y - f x‖) :
    HasDerivAt g 0 x := by
  have hsmall : (fun y => f y - f x) =o[𝓝 x] (fun y => y - x) := by
    simpa only [smul_zero, sub_zero] using hf.isLittleO
  have hbig : (fun y => g y - g x) =O[𝓝 x] (fun y => f y - f x) :=
    IsBigO.of_bound C hbound
  apply HasDerivAt.of_isLittleO
  simpa only [smul_zero, sub_zero] using hbig.trans_isLittleO hsmall

theorem fderiv_apply_eq_zero_of_increment_bound {f : E → F} {g : E → G}
    {x : E} {C : ℝ} (hf : DifferentiableAt ℝ f x)
    (hbound : ∀ᶠ y in 𝓝 x, ‖g y - g x‖ ≤ C * ‖f y - f x‖)
    {v : E} (hv : fderiv ℝ f x v = 0) : fderiv ℝ g x v = 0 := by
  by_cases hg : DifferentiableAt ℝ g x
  · let delta := fun t : ℝ => x + t • v
    have hd : HasDerivAt delta v 0 := by
      simpa +instances only [one_smul] using!
        ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    have hd0 : delta 0 = x := by simp [delta]
    have hf0 : HasFDerivAt f (fderiv ℝ f x) (delta 0) := by
      simpa only [hd0] using hf.hasFDerivAt
    have hg0 : HasFDerivAt g (fderiv ℝ g x) (delta 0) := by
      simpa only [hd0] using hg.hasFDerivAt
    have hfd : HasDerivAt (f ∘ delta) 0 0 := by
      simpa only [hv] using hf0.comp_hasDerivAt 0 hd
    have hgd : HasDerivAt (g ∘ delta) (fderiv ℝ g x v) 0 := by
      exact hg0.comp_hasDerivAt 0 hd
    have hb : ∀ᶠ t in 𝓝 (0 : ℝ),
        ‖(g ∘ delta) t - (g ∘ delta) 0‖ ≤ C * ‖(f ∘ delta) t - (f ∘ delta) 0‖ := by
      filter_upwards [hd.continuousAt.tendsto.eventually (hd0.symm ▸ hbound)] with t ht
      simpa only [Function.comp_apply, hd0] using ht
    exact hgd.unique (hasDerivAt_zero_of_increment_bound hfd hb)
  · rw [fderiv_zero_of_not_differentiableAt hg]
    exact zero_apply _

end PoincareConjecture.M60
