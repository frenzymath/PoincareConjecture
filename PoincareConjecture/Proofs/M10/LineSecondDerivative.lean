import PoincareConjecture.Proofs.M10.ScalarUpperContacts
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.CompCLM









set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem second_deriv_affine_line {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (v : E) :
    deriv (deriv (fun t : ℝ ↦ f (x + t • v))) 0 =
      fderiv ℝ (fderiv ℝ f) x v v := by
  let L := fun t : ℝ ↦ x + t • v
  have hL (t : ℝ) : HasDerivAt L v t := by
    simpa only [L, id_eq, one_smul] using ((hasDerivAt_id t).smul_const v).const_add x
  have hL0 : L 0 = x := by simp [L]
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (L t) := by
    have he := (hf.eventually (by norm_num)).mono (fun y hy ↦ hy.differentiableAt two_ne_zero)
    have ht : Tendsto L (𝓝 0) (𝓝 x) := by
      simpa only [hL0] using (hL 0).continuousAt.tendsto
    exact ht he
  have hderiv : deriv (fun t ↦ f (L t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t ↦ fderiv ℝ f (L t) v) := by
    filter_upwards [hnear] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hL t)).deriv
  rw [hderiv.deriv_eq]
  have hD := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hD' : DifferentiableAt ℝ (fderiv ℝ f) (L 0) := by rwa [hL0]
  have hd := (hD'.hasFDerivAt.comp_hasDerivAt 0 (hL 0)).clm_apply (hasDerivAt_const 0 v)
  simpa only [hL0, map_zero, add_zero, Function.comp_def] using hd.deriv


theorem second_fderiv_nonneg_of_isLocalMin {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hmin : IsLocalMin f x) (v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  let L := fun t : ℝ ↦ x + t • v
  have hL : ContinuousAt L 0 := by dsimp [L]; fun_prop
  have hzero : L 0 = x := by simp [L]
  have hmin' : IsLocalMin f (L 0) := by rwa [hzero]
  have hcont : ContinuousAt (fun t ↦ f (L t)) 0 := by
    have hf' : ContinuousAt f (L 0) := by simpa only [hzero] using hf.continuousAt
    exact hf'.comp hL
  by_contra! hneg
  rw [← second_deriv_affine_line hf v] at hneg
  exact not_isLocalMin_of_strict_upper_contact rfl (Filter.Eventually.of_forall (fun _ ↦ le_rfl))
    hcont hneg (hmin'.comp_continuous hL)

end PoincareConjecture.M10
