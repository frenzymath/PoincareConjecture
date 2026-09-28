import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Composition
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [IsManifold (𝓡 n) ∞ M] in
private theorem scalar_mvfderiv_comp {f : M → ℝ} {F : ℝ → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hF : DifferentiableAt ℝ F (f x)) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (F ∘ f) x v = deriv F (f x) * mvfderiv (𝓡 n) f x v := by
  rw [mvfderiv_comp x hF.mdifferentiableAt hf]
  simp only [ContinuousLinearMap.comp_apply, mvfderiv, mfderiv_eq_fderiv]
  rw [hF.hasDerivAt.hasFDerivAt.fderiv]
  change mvfderiv (𝓡 n) f x v * deriv F (f x) = _
  exact mul_comm _ _

theorem hessian_one_sub_exp_neg (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (u v : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => 1 - Real.exp (-f y)) x u v =
      Real.exp (-f x) *
        (D.hessian f x u v - mvfderiv (𝓡 n) f x u * mvfderiv (𝓡 n) f x v) := by
  let F : ℝ → ℝ := fun s => 1 - Real.exp (-s)
  have hF : ContDiff ℝ ∞ F := by fun_prop
  have hFd : deriv F = fun s => Real.exp (-s) := by
    funext s
    have hd : HasDerivAt F (Real.exp (-s)) s := by
      simpa [F] using
        (((hasDerivAt_id s).neg).exp).const_sub 1
    exact hd.deriv
  have hdexp (s : ℝ) : deriv (fun r => Real.exp (-r)) s = -Real.exp (-s) := by
    simpa using (((hasDerivAt_id s).neg).exp).deriv
  have hcomp := hF.contMDiff.contMDiffAt.comp x hf
  have hdf := (hF.deriv' (n := ∞)).contMDiff.contMDiffAt.comp x hf
  have hgf := (D.contMDiffAt_gradient hf).mdifferentiableAt (by simp)
  have hfn := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hf.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
  have heq : D.gradient (F ∘ f) =ᶠ[𝓝 x] (deriv F ∘ f) • D.gradient f := by
    filter_upwards [hfn] with y hy
    exact D.gradient_comp (hy.mdifferentiableAt (by simp))
      (hF.differentiable (by simp) (f y))
  have hc := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    ((D.contMDiffAt_gradient hcomp).mdifferentiableAt (by simp))
    ((hdf.mdifferentiableAt (by simp)).smul_section hgf) (by simp) heq
  change D.hessian (F ∘ f) x u v = _
  rw [D.hessian_eq_inner_connection_gradient hcomp,
    congrArg (fun L => L u) hc,
    D.connection.isCovariantDerivativeOn.leibniz hgf (hdf.mdifferentiableAt (by simp)),
    D.hessian_eq_inner_connection_gradient hf]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, smul_eq_mul, Function.comp_apply, D.inner_gradient]
  rw [scalar_mvfderiv_comp (hf.mdifferentiableAt (by simp))
    ((hF.deriv' (n := ∞)).differentiable (by simp) (f x)), hFd, hdexp]
  ring

theorem hessian_one_sub_exp_neg_le_of_transverse_bound
    (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (w : TangentSpace (𝓡 n) x) {a : ℝ} (ha : a ≤ 1)
    (hbound : D.hessian f x w w ≤
      -a * (g.inner x w w - (mvfderiv (𝓡 n) f x w) ^ 2)) :
    D.hessian (fun y => 1 - Real.exp (-f y)) x w w ≤
      -Real.exp (-f x) * a * g.inner x w w := by
  rw [D.hessian_one_sub_exp_neg hf]
  have hcorrection : (1 - a) * (mvfderiv (𝓡 n) f x w) ^ 2 ≥ 0 :=
    mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg _)
  have hquad : D.hessian f x w w -
      mvfderiv (𝓡 n) f x w * mvfderiv (𝓡 n) f x w ≤ -a * g.inner x w w := by
    nlinarith only [hbound, hcorrection]
  calc
    _ ≤ Real.exp (-f x) * (-a * g.inner x w w) :=
      mul_le_mul_of_nonneg_left hquad (Real.exp_pos _).le
    _ = _ := by ring

theorem hessian_one_sub_exp_neg_neg_of_transverse_bound
    (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    {w : TangentSpace (𝓡 n) x} (hw : w ≠ 0) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hbound : D.hessian f x w w ≤
      -a * (g.inner x w w - (mvfderiv (𝓡 n) f x w) ^ 2)) :
    D.hessian (fun y => 1 - Real.exp (-f y)) x w w < 0 := by
  apply (D.hessian_one_sub_exp_neg_le_of_transverse_bound hf w ha1 hbound).trans_lt
  have hpositive := mul_pos (mul_pos (Real.exp_pos (-f x)) ha) (g.pos x w hw)
  nlinarith only [hpositive]

end PoincareConjecture.LeviCivitaData
