import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Normed.Module.RCLike.Real

set_option autoImplicit false

open Set Metric

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

theorem fderiv_eq_zero_of_eqOn_outer_annulus
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    {f : E → F} {c : F} {r : Real} (hr : 1 < r)
    (hconst : EqOn f (fun _ => c) (closedBall (0 : E) r \ ball 0 1))
    {q : E} (hq : q ∈ sphere (0 : E) 1) (hf : DifferentiableAt Real f q) :
    fderiv Real f q = 0 := by
  let δ : Real := (r - 1) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let b : E := (1 + δ) • q
  have hqn : ‖q‖ = 1 := mem_sphere_zero_iff_norm.mp hq
  have hbn : ‖b‖ = 1 + δ := by
    simp only [b, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + δ),
      hqn, mul_one]
  have hqb : dist q b = δ := by
    rw [dist_eq_norm, show q - b = (-δ) • q by
      dsimp [b]
      module]
    simp [norm_smul, Real.norm_eq_abs, hqn, abs_of_pos hδ]
  have hqB : q ∈ closedBall b δ := mem_closedBall.mpr hqb.le
  have hB : closedBall b δ ⊆ closedBall (0 : E) r \ ball 0 1 := by
    intro x hx
    have hxb : ‖x - b‖ ≤ δ := by simpa only [mem_closedBall, dist_eq_norm] using hx
    have hupper := norm_le_norm_sub_add x b
    have hlower := norm_le_norm_sub_add b x
    rw [norm_sub_rev b x] at hlower
    rw [hbn] at hupper hlower
    refine ⟨mem_closedBall_zero_iff.mpr ?_, ?_⟩
    · dsimp [δ] at hxb hupper hlower
      linarith
    · rw [mem_ball_zero_iff]
      linarith
  have hunique : UniqueDiffWithinAt Real (closedBall b δ) q :=
    uniqueDiffWithinAt_convex (convex_closedBall b δ)
      (by rw [interior_closedBall b hδ.ne']; exact ⟨b, mem_ball_self hδ⟩)
      (subset_closure hqB)
  exact hunique.eq hf.hasFDerivAt.hasFDerivWithinAt
    ((hasFDerivWithinAt_const c q (closedBall b δ)).congr'
      (fun x hx => hconst (hB hx)) hqB)

theorem fderiv_eq_of_eqOn_outer_annulus
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    {f g : E → F} {r : Real} (hr : 1 < r)
    (heq : EqOn f g (closedBall (0 : E) r \ ball 0 1))
    {q : E} (hq : q ∈ sphere (0 : E) 1)
    (hf : DifferentiableAt Real f q) (hg : DifferentiableAt Real g q) :
    fderiv Real f q = fderiv Real g q := by
  have hzero : fderiv Real (fun x => f x - g x) q = 0 :=
    fderiv_eq_zero_of_eqOn_outer_annulus hr
      (fun x hx => sub_eq_zero.mpr (heq hx)) hq (hf.sub hg)
  change fderiv Real (f - g) q = 0 at hzero
  rw [fderiv_sub hf hg] at hzero
  exact sub_eq_zero.mp hzero

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
