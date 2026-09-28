import PoincareConjecture.Proofs.Horizon.Analysis.ODE.CompactConfinement

noncomputable section

namespace Poincare.ODE

open Set Metric
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dist_le_of_solution_bounded_speed
    {U : Set E} {F : E → E} {C T : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ y ∈ U, ‖F y‖ ≤ C) {γ : ℝ → E}
    (hγ : ∀ t ∈ Icc 0 T, γ t ∈ U ∧
      HasDerivWithinAt γ (F (γ t)) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) : dist (γ t) (γ 0) ≤ C * t := by
  have hlip := (convex_Icc (0 : ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (C := ⟨C, hC⟩) (fun s hs => (hγ s hs).2)
    (fun s hs => show ‖F (γ s)‖₊ ≤ ⟨C, hC⟩ from hbound (γ s) (hγ s hs).1)
  have hb : dist (γ t) (γ 0) ≤ C * dist t 0 :=
    hlip.dist_le_mul t ht 0 ⟨le_rfl, ht.1.trans ht.2⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg ht.1] using hb

variable [FiniteDimensional ℝ E]

theorem exists_solution_of_bounded_speed
    {U : Set E} (hU : IsOpen U) {F : E → E} (hF : ContDiffOn ℝ ∞ F U)
    {p x : E} {R C T : ℝ} (hball : closedBall p R ⊆ U)
    (hC : 0 ≤ C) (hbound : ∀ y ∈ U, ‖F y‖ ≤ C) (hT : 0 ≤ T)
    (hmargin : dist x p + C * T ≤ R) :
    ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Icc 0 T, γ t ∈ U ∧ dist (γ t) p ≤ dist x p + C * t ∧
        HasDerivWithinAt γ (F (γ t)) (Icc 0 T) t := by
  have hx : x ∈ closedBall p R := by
    apply (mem_closedBall).mpr
    nlinarith [mul_nonneg hC hT]
  have hdist {t : ℝ} {γ : ℝ → E} (hinit : γ 0 = x)
      (hγ : ∀ r ∈ Icc 0 t, γ r ∈ U ∧ HasDerivWithinAt γ (F (γ r)) (Icc 0 t) r)
      (ht : 0 ≤ t) : dist (γ t) p ≤ dist x p + C * t := by
    have hb := dist_le_of_solution_bounded_speed hC hbound hγ ⟨ht, le_rfl⟩
    have hh := dist_triangle (γ t) (γ 0) p
    rw [hinit] at hb hh
    linarith
  obtain ⟨γ, hinit, hγ⟩ := exists_solution_of_compact_confinement hU
    (isCompact_closedBall p R) hball hF hx hT (fun t ht γ hinit hγ => by
      apply (hdist hinit hγ ht.1).trans
      nlinarith [mul_le_mul_of_nonneg_left ht.2 hC])
  refine ⟨γ, hinit, fun t ht => ⟨(hγ t ht).1, ?_, (hγ t ht).2⟩⟩
  exact hdist hinit (fun r hr => ⟨(hγ r ⟨hr.1, hr.2.trans ht.2⟩).1,
    (hγ r ⟨hr.1, hr.2.trans ht.2⟩).2.mono (Icc_subset_Icc_right ht.2)⟩) ht.1

end Poincare.ODE
