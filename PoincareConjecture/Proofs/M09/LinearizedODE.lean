import PoincareConjecture.Proofs.M09.MixedPartials
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false

open scoped ContDiff Topology
open Filter

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_variation_of_ode (f : ℝ × ℝ → E) (B : ℝ × E → E) (s : ℝ)
    (hf : ContDiffAt ℝ ∞ f (s, 0))
    (hB : DifferentiableAt ℝ B (s, f (s, 0)))
    (hode : ∀ᶠ u in 𝓝 (0 : ℝ),
      HasDerivAt (fun r ↦ f (r, u)) (B (s, f (s, u))) s) :
    HasDerivAt (fun r ↦ deriv (fun u ↦ f (r, u)) 0)
      (fderiv ℝ B (s, f (s, 0)) (0, deriv (fun u ↦ f (s, u)) 0)) s := by
  let Y : ℝ → E := fun r ↦ deriv (fun u ↦ f (r, u)) 0
  let w := fderiv ℝ B (s, f (s, 0)) (0, Y s)
  have hu : HasDerivAt (fun u ↦ f (s, u)) (Y s) 0 :=
    (hasDerivAt_slice_snd f s 0 (hf.differentiableAt (by simp))).differentiableAt.hasDerivAt
  have hk : HasDerivAt (fun u ↦ B (s, f (s, u))) w 0 :=
    hB.hasFDerivAt.comp_hasDerivAt 0 ((hasDerivAt_const 0 s).prodMk hu)
  have htrans : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ ↦ (s + z.1, z.2)) (0, 0) :=
    (contDiff_const.add contDiff_fst).prodMk contDiff_snd |>.contDiffAt
  have hF : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ ↦ f (s + z.1, z.2)) (0, 0) := by
    have hf' : ContDiffAt ℝ ∞ f (s + 0, 0) := by simpa only [add_zero] using hf
    exact hf'.comp (0, 0) htrans
  have hjet : ∀ᶠ u in 𝓝 (0 : ℝ),
      HasDerivAt (fun r ↦ f (s + r, u)) (B (s, f (s, u))) 0 := by
    filter_upwards [hode] with u hu
    simpa only [Function.comp_def, id_eq, one_smul] using hu.scomp_of_eq 0
      ((hasDerivAt_id 0).const_add s) (add_zero s).symm
  have hY : HasDerivAt (fun r ↦ Y (s + r)) w 0 :=
    hasDerivAt_partial_snd_of_initial_fst (fun z : ℝ × ℝ ↦ f (s + z.1, z.2))
      hF (fun u ↦ B (s, f (s, u))) w hk hjet
  have hback := hY.scomp_of_eq s ((hasDerivAt_id s).sub_const s) (sub_self s).symm
  have hcancel (r : ℝ) : s + (r - s) = r := by ring
  simpa only [Function.comp_def, id_eq, one_smul, hcancel, Y, w] using hback

end PoincareConjecture.Proofs.M09
