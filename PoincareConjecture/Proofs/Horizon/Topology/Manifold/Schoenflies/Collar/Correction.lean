import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

namespace Poincare.Manifold.Schoenflies

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

def correctNormal (G N : E -> F) (x : E) : F :=
  G x + ((‖x‖ ^ 2 - 1) / 2) • (N x - fderiv Real G x x)

theorem correctNormal_sphere (G N : E -> F) {p : E} (hp : ‖p‖ = 1) :
    correctNormal G N p = G p := by
  simp [correctNormal, hp]

theorem contDiff_correctNormal {G N : E -> F}
    (hG : ContDiff Real ∞ G) (hN : ContDiff Real ∞ N) :
    ContDiff Real ∞ (correctNormal G N) := by
  have hd : ContDiff Real ∞ (fun x => fderiv Real G x x) :=
    (hG.fderiv_right (by simp)).clm_apply contDiff_id
  exact hG.add (((((contDiff_id (𝕜 := Real) (E := E)).norm_sq (𝕜 := Real)).sub
    contDiff_const).div_const 2).smul (hN.sub hd))

theorem fderiv_correctNormal {G N : E -> F}
    (hG : ContDiff Real ∞ G) (hN : ContDiff Real ∞ N)
    {p : E} (hp : ‖p‖ = 1) (v : E) :
    fderiv Real (correctNormal G N) p v =
      fderiv Real G p (v - inner Real p v • p) + inner Real p v • N p := by
  have hd : DifferentiableAt Real (fun x => N x - fderiv Real G x x) p :=
    (hN.sub ((hG.fderiv_right (by simp)).clm_apply contDiff_id)).differentiable
      (by simp) p
  have hs : HasFDerivAt (fun x : E => (‖x‖ ^ 2 - 1) / 2) (innerSL Real p) p := by
    convert ((hasStrictFDerivAt_norm_sq p).hasFDerivAt.sub_const 1).const_smul
      (2⁻¹ : Real) using 1
    all_goals first | rfl | (ext x; simp [div_eq_mul_inv, mul_comm])
  have h := ((hG.differentiable (by simp) p).hasFDerivAt.add (hs.smul hd.hasFDerivAt)).fderiv
  rw [show fderiv Real (correctNormal G N) p = _ from h]
  simp only [add_apply,
    hp, one_pow, sub_self, zero_div, zero_smul, zero_add,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    map_sub, map_smul, smul_sub]
  abel

end Poincare.Manifold.Schoenflies
