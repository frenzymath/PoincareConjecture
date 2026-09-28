import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring









set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

namespace Poincare.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


lemma fderiv_fderiv_comp_smul (f : E → ℝ) (r : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ f (r • y))) x =
      r ^ 2 • fderiv ℝ (fderiv ℝ f) (r • x) := by
  have h : fderiv ℝ (fun y ↦ f (r • y)) =
      r • (fun y ↦ fderiv ℝ f (r • y)) := by
    funext y
    exact fderiv_comp_smul r
  rw [h, fderiv_const_smul_field]
  simp only [Pi.smul_apply, fderiv_comp_smul, smul_smul, pow_two]



lemma norm_fderiv_fderiv_le_of_rescaled (f : E → ℝ) {r B : ℝ} (hr : 0 < r)
    (hbound : ‖fderiv ℝ (fderiv ℝ (fun y ↦ f (r • y))) 0‖ ≤ B) :
    ‖fderiv ℝ (fderiv ℝ f) 0‖ ≤ B / r ^ 2 := by
  rw [fderiv_fderiv_comp_smul, smul_zero, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)] at hbound
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  simpa only [mul_comm] using hbound



lemma smul_mem_ball (x : E) {r R : ℝ} (hr : 0 < r) (hx : x ∈ Metric.ball 0 R) :
    r • x ∈ Metric.ball 0 (r * R) := by
  simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr] at hx ⊢
  exact mul_lt_mul_of_pos_left hx hr


lemma contDiffOn_spatially_rescaled {f : E → ℝ → ℝ} {r R : ℝ} (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ (fun z : E × ℝ ↦ f z.1 z.2)
      (Metric.ball 0 (r * R) ×ˢ Set.Ioi 0)) :
    ContDiffOn ℝ ∞ (fun z : E × ℝ ↦ f (r • z.1) z.2)
      (Metric.ball 0 R ×ˢ Set.Ioi 0) := by
  have hmap : ContDiffOn ℝ ∞ (fun z : E × ℝ ↦ (r • z.1, z.2))
      (Metric.ball 0 R ×ˢ Set.Ioi 0) :=
    (contDiffOn_fst.const_smul r).prodMk contDiffOn_snd
  exact hf.comp hmap (fun z hz ↦ ⟨smul_mem_ball z.1 hr hz.1, hz.2⟩)



lemma hasDerivAt_spatially_rescaled_heat {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ → ℝ)
    (a : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    {r t : ℝ} (hr : r ≠ 0) (x : EuclideanSpace ℝ (Fin n))
    (hheat : HasDerivAt (fun s ↦ f (r • x) s)
      (∑ i, ∑ j, a (r • x) i j * fderiv ℝ (fderiv ℝ (fun y ↦ f y t)) (r • x)
        (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j)) t) :
    HasDerivAt (fun s ↦ f (r • x) s)
      (∑ i, ∑ j, (a (r • x) i j / r ^ 2) *
        fderiv ℝ (fderiv ℝ (fun y ↦ f (r • y) t)) x
          (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)) t := by
  convert hheat using 1
  rw [fderiv_fderiv_comp_smul (fun y ↦ f y t) r x]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_apply, smul_eq_mul]
  field_simp

end Poincare.Parabolic
