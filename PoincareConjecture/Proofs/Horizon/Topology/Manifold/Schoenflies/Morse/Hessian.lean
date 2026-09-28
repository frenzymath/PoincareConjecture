import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.CompCLM



noncomputable section
set_option autoImplicit false

open scoped ContDiff

namespace Poincare.Manifold.Schoenflies

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [InnerProductSpace Real F]

theorem height_hessian_apply
    {g : E -> F} (hg : ContDiff Real ∞ g) (w : F) (a u v : E) :
    fderiv Real (fderiv Real (fun x => inner Real w (g x))) a v u =
      inner Real w (fderiv Real (fderiv Real g) a v u) := by
  have hfirst : fderiv Real (fun x => inner Real w (g x)) =
      fun x => (innerSL Real w).comp (fderiv Real g x) := by
    funext x
    exact ((innerSL Real w).hasFDerivAt.comp x
      (hg.differentiable (by simp) x).hasFDerivAt).fderiv
  rw [hfirst, fderiv_clm_comp (differentiableAt_const _)
    ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp) a)]
  simp

theorem derivative_normal_orthogonality
    {g n : E -> F} (hg : ContDiff Real ∞ g) (hn : ContDiff Real ∞ n)
    (horth : ∀ x u, inner Real (n x) (fderiv Real g x u) = 0)
    (a u v : E) :
    inner Real (n a) (fderiv Real (fderiv Real g) a v u) +
      inner Real (fderiv Real n a v) (fderiv Real g a u) = 0 := by
  have hdg : Differentiable Real (fderiv Real g) :=
    (hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have heq : (fun x => inner Real (n x) (fderiv Real g x u)) = fun _ => 0 :=
    funext fun x => horth x u
  have h := fderiv_inner_apply Real (hn.differentiable (by simp) a)
    ((hdg a).clm_apply (differentiableAt_const u)) v
  rw [heq] at h
  rw [fderiv_clm_apply (hdg a) (differentiableAt_const _)] at h
  simpa using h.symm

theorem derivative_unit_normal_orthogonal
    {n : E -> F} (hn : ContDiff Real ∞ n) (hunit : ∀ x, ‖n x‖ = 1) (a v : E) :
    inner Real (fderiv Real n a v) (n a) = 0 := by
  have heq : (fun x => inner Real (n x) (n x)) = fun _ => 1 := by
    funext x
    simp [hunit x]
  have h := fderiv_inner_apply Real (hn.differentiable (by simp) a)
    (hn.differentiable (by simp) a) v
  rw [heq] at h
  simp only [fderiv_const_apply, zero_apply] at h
  rw [real_inner_comm (n a)] at h
  rw [real_inner_comm]
  linarith



theorem injective_height_hessian_of_regular_normal
    {g n : E -> F} (hg : ContDiff Real ∞ g) (hn : ContDiff Real ∞ n)
    (hunit : ∀ x, ‖n x‖ = 1)
    (horth : ∀ x u, inner Real (n x) (fderiv Real g x u) = 0)
    (a : E)
    (hspan : ∀ w, (∀ u, inner Real w (fderiv Real g a u) = 0) ->
      ∃ c : Real, w = c • n a)
    (hinj : Function.Injective (fderiv Real n a)) :
    Function.Injective (fderiv Real (fderiv Real (fun x => inner Real (n a) (g x))) a) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hvzero : ∀ u, inner Real (n a) (fderiv Real (fderiv Real g) a v u) = 0 := by
    intro u
    rw [← height_hessian_apply hg]
    exact congrArg (fun L : E →L[Real] Real => L u) hv
  have hnormal : ∀ u, inner Real (fderiv Real n a v) (fderiv Real g a u) = 0 := by
    intro u
    have h := derivative_normal_orthogonality hg hn horth a u v
    rw [hvzero u, zero_add] at h
    exact h
  obtain ⟨c, hc⟩ := hspan (fderiv Real n a v) hnormal
  have hperp := derivative_unit_normal_orthogonal hn hunit a v
  have hc0 : c = 0 := by
    simpa [hc, real_inner_smul_left, real_inner_self_eq_norm_sq, hunit a] using hperp
  apply hinj
  simp [hc, hc0]

end Poincare.Manifold.Schoenflies
