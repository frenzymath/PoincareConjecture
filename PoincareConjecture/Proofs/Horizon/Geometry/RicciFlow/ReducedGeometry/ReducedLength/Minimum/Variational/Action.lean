import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.PathCompactness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture.ReducedLengthMinimum.Variational

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def regularizedLIntegrand {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (α : ℝ → M) (s : ℝ) : ℝ :=
  2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (α s) +
    (1 / 2 : ℝ) * (F.metric (T - s ^ 2)).inner (α s)
      (curveVelocity (n := n) α s) (curveVelocity (n := n) α s)

noncomputable def regularizedLAction {J : Set ℝ} (F : RicciFlow n M J)
    (T tau : ℝ) (α : ℝ → M) : ℝ :=
  ∫ s in 0..Real.sqrt tau, regularizedLIntegrand F T α s

theorem squarePath_integrand_eq_transformed {J : Set ℝ} {F : RicciFlow n M J}
    {T tau : ℝ} (p : BackwardTimePath F T 0 tau)
    {s : ℝ} (hs : s ∈ Ioo 0 (Real.sqrt tau)) :
    regularizedLIntegrand F T (fun r => p.curve (r ^ 2)) s =
      backwardLIntegrand F T p.curve (s ^ 2) * (2 * s) := by
  have htime : s ^ 2 ∈ Ioo 0 tau :=
    ⟨sq_pos_of_pos hs.1, (Real.lt_sqrt hs.1.le).mp hs.2⟩
  have hreg := (p.regular _ htime).contMDiffAt (isOpen_Ioo.mem_nhds htime)
  have hvel := curveVelocity_comp_sq (hreg.mdifferentiableAt one_ne_zero)
  unfold regularizedLIntegrand backwardLIntegrand
  rw [Real.sqrt_sq hs.1.le, hvel]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

theorem squarePath_action {J : Set ℝ} {F : RicciFlow n M J}
    {T tau : ℝ} (p : BackwardTimePath F T 0 tau) :
    IntervalIntegrable (regularizedLIntegrand F T (fun r => p.curve (r ^ 2)))
      volume 0 (Real.sqrt tau) ∧
    regularizedLAction F T tau (fun r => p.curve (r ^ 2)) =
      backwardLLength F T 0 tau p.curve := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => r ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hn : ∀ s ∈ uIoo 0 (Real.sqrt tau), 0 ≤ 2 * s := by
    intro s hs
    rw [uIoo_of_le (Real.sqrt_nonneg tau)] at hs
    exact mul_nonneg (by norm_num) hs.1.le
  have ht : IntervalIntegrable
      (fun s => backwardLIntegrand F T p.curve (s ^ 2) * (2 * s))
      volume 0 (Real.sqrt tau) := by
    apply (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      (f := fun s : ℝ => s ^ 2) (f' := fun s => 2 * s)
      (g := backwardLIntegrand F T p.curve)
      (continuous_id.pow 2).continuousOn (fun s _ => hd s) hn).mpr
    simpa only [zero_pow two_ne_zero, Real.sq_sqrt p.ordered.le] using p.l_integrable
  refine ⟨?_, ?_⟩
  · apply ht.congr_uIoo
    intro s hs
    rw [uIoo_of_le (Real.sqrt_nonneg tau)] at hs
    exact (squarePath_integrand_eq_transformed p hs).symm
  · have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (f := fun s : ℝ => s ^ 2) (f' := fun s => 2 * s)
      (g := backwardLIntegrand F T p.curve)
      (continuous_id.pow 2).continuousOn (fun s _ => hd s) hn
    calc
      _ = ∫ s in 0..Real.sqrt tau,
          backwardLIntegrand F T p.curve (s ^ 2) * (2 * s) :=
        intervalIntegral.integral_congr_Ioo_of_le (Real.sqrt_nonneg tau)
          (fun _ hs => squarePath_integrand_eq_transformed p hs)
      _ = _ := by
        simpa only [Function.comp_def, zero_pow two_ne_zero,
          Real.sq_sqrt p.ordered.le, backwardLLength] using hsub

end PoincareConjecture.ReducedLengthMinimum.Variational
