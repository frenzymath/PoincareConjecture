import Mathlib.Analysis.Calculus.ContDiff.Operations









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M60

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem second_fderiv_congr {f g : E → F} {p : E}
    (h : f =ᶠ[𝓝 p] g) (u v : E) :
    fderiv ℝ (fun q => fderiv ℝ f q u) p v =
      fderiv ℝ (fun q => fderiv ℝ g q u) p v := by
  have h' : fderiv ℝ f =ᶠ[𝓝 p] fderiv ℝ g := h.fderiv
  have heq : (fun q => fderiv ℝ f q u) =ᶠ[𝓝 p] (fun q => fderiv ℝ g q u) :=
    h'.mono fun q hq => congrArg (fun L => L u) hq
  rw [heq.fderiv_eq]



theorem second_fderiv_sub {f g : E → F} {p : E}
    (hf : ContDiffAt ℝ 2 f p) (hg : ContDiffAt ℝ 2 g p) (u v : E) :
    fderiv ℝ (fun q => fderiv ℝ (fun r => f r - g r) q u) p v =
      fderiv ℝ (fun q => fderiv ℝ f q u) p v -
        fderiv ℝ (fun q => fderiv ℝ g q u) p v := by
  have heq : (fun q => fderiv ℝ (fun r => f r - g r) q u) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ f q u - fderiv ℝ g q u) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with q hfq hgq
    rw [fderiv_fun_sub (hfq.differentiableAt (by norm_num))
      (hgq.differentiableAt (by norm_num)), sub_apply]
  have hdf : DifferentiableAt ℝ (fun q => fderiv ℝ f q u) p :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hdg : DifferentiableAt ℝ (fun q => fderiv ℝ g q u) p :=
    ((hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  rw [heq.fderiv_eq, fderiv_fun_sub hdf hdg, sub_apply]

end PoincareConjecture.M60
