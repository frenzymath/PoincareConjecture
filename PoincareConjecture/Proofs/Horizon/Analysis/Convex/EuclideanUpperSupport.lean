import PoincareConjecture.Proofs.Horizon.Analysis.Convex.UpperSupport
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

namespace Poincare.Analysis

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem second_deriv_comp_lineMap {u : E → ℝ} {x y : E} {t : ℝ}
    (hu : ContDiffAt ℝ 2 u (AffineMap.lineMap x y t)) :
    deriv (deriv (u ∘ AffineMap.lineMap x y)) t =
      fderiv ℝ (fderiv ℝ u) (AffineMap.lineMap x y t) (y - x) (y - x) := by
  let L : ℝ → E := AffineMap.lineMap x y
  have hL (s : ℝ) : HasDerivAt L (y - x) s := AffineMap.hasDerivAt_lineMap
  have hfirst : deriv (u ∘ L) =ᶠ[𝓝 t] fun s => fderiv ℝ u (L s) (y - x) := by
    filter_upwards [(hL t).continuousAt.eventually (hu.eventually (by norm_num))] with s hs
    exact (hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s (hL s) |>.deriv
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) (L t) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsecond := (hdu.hasFDerivAt.comp_hasDerivAt t (hL t)).clm_apply
    (hasDerivAt_const t (y - x))
  rw [hfirst.deriv_eq]
  simpa using hsecond.deriv

theorem concaveOn_of_hessian_upper_support {s : Set E} {f : E → ℝ}
    (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hsupport : ∀ x ∈ s, ∃ u : E → ℝ, ContDiffAt ℝ 2 u x ∧ u x = f x ∧
      (∀ᶠ y in 𝓝 x, f y ≤ u y) ∧
      ∀ v : E, fderiv ℝ (fderiv ℝ u) x v v ≤ 0) :
    ConcaveOn ℝ s f := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  let L : ℝ → E := AffineMap.lineMap x y
  have hL : Continuous L := by dsimp [L]; fun_prop
  have hmem : MapsTo L (Icc 0 1) s := fun t ht => hs.lineMap_mem hx hy ht
  have hc : ConcaveOn ℝ (Icc (0 : ℝ) 1) (f ∘ L) := by
    apply concaveOn_of_approximate_upper_support
      (hf.comp hL.continuousOn hmem)
    intro t ht ε hε
    obtain ⟨u, hu, htouch, hupper, hsecond⟩ :=
      hsupport (L t) (hmem ⟨ht.1.le, ht.2.le⟩)
    refine ⟨u ∘ L, hu.comp t (by
      change ContDiffAt ℝ 2 (fun z : ℝ => z • (y - x) + x) t
      fun_prop), htouch,
      (hL.continuousAt.eventually hupper), ?_⟩
    rw [second_deriv_comp_lineMap hu]
    exact (hsecond (y - x)).trans hε.le
  have h := hc.2 (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) ha hb hab
  have haeq : 1 - b = a := by linarith
  have heq : b • (y - x) + x = a • x + b • y := by
    rw [← haeq, sub_smul, one_smul, smul_sub]
    abel
  simpa [L, Function.comp_def, AffineMap.lineMap_apply, heq] using h

end Normed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem concaveOn_sub_norm_sq_of_hessian_upper_support
    {s : Set E} {f : E → ℝ} {C : ℝ}
    (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hsupport : ∀ x ∈ s, ∃ u : E → ℝ, ContDiffAt ℝ 2 u x ∧ u x = f x ∧
      (∀ᶠ y in 𝓝 x, f y ≤ u y) ∧
      ∀ v : E, fderiv ℝ (fderiv ℝ u) x v v ≤ C * ‖v‖ ^ 2) :
    ConcaveOn ℝ s (fun x => f x - C * ‖x‖ ^ 2 / 2) := by
  let q : E → ℝ := fun x => C * ‖x‖ ^ 2 / 2
  have hqc : ContDiff ℝ 2 q := by
    exact (contDiff_const.mul (contDiff_norm_sq ℝ)).div_const 2
  have hqd (x : E) : HasFDerivAt q (C • innerSL ℝ x) x := by
    have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.fun_const_smul (C / 2)
    have hcoef : (C / 2) • (2 • innerSL ℝ x) = C • innerSL ℝ x := by
      ext v
      simp
      ring
    rw [hcoef] at h
    simpa only [q, smul_eq_mul, div_mul_eq_mul_div] using h
  have hqfirst : fderiv ℝ q = fun x => C • innerSL ℝ x :=
    funext fun x => (hqd x).fderiv
  have hqsecond (x v : E) : fderiv ℝ (fderiv ℝ q) x v v = C * ‖v‖ ^ 2 := by
    rw [hqfirst, ((innerSL ℝ).hasFDerivAt.fun_const_smul C).fderiv]
    change C * inner ℝ v v = C * ‖v‖ ^ 2
    rw [real_inner_self_eq_norm_sq]
  apply concaveOn_of_hessian_upper_support hs (hf.sub hqc.continuous.continuousOn)
  intro x hx
  obtain ⟨u, hu, htouch, hupper, hbound⟩ := hsupport x hx
  refine ⟨fun y => u y - q y, hu.sub hqc.contDiffAt, by simp [htouch],
    hupper.mono (fun y hy => sub_le_sub_right hy (q y)), ?_⟩
  intro v
  have hfirst : fderiv ℝ (fun y => u y - q y) =ᶠ[𝓝 x]
      fun y => fderiv ℝ u y - fderiv ℝ q y := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    exact fderiv_sub (hy.differentiableAt (by norm_num))
      (hqc.differentiable (by norm_num) y)
  rw [hfirst.fderiv_eq, fderiv_fun_sub
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    (((hqc.contDiffAt).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))]
  simp only [sub_apply, hqsecond]
  exact sub_nonpos.mpr (hbound v)

end Poincare.Analysis
