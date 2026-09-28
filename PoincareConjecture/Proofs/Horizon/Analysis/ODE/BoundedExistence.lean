import PoincareConjecture.Proofs.Horizon.Analysis.ODE.BoundedSpeedSmooth
import PoincareConjecture.Proofs.Horizon.Analysis.ODE.Forward










noncomputable section
set_option autoImplicit false

open Set Metric
open scoped ContDiff

namespace Poincare.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]



theorem exists_forward_solution_of_bounded_speed
    {F : E → E} (hF : ContDiff ℝ ∞ F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖F x‖ ≤ C) (x : E) :
    ∃ δ > 0, ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Ioi (-δ), HasDerivAt γ (F (γ t)) t := by
  obtain ⟨δ, hδ, γ, hγ0, hγ, _⟩ :=
    exists_forward_solution_of_finite_solutions (U := univ) (K := univ)
      isOpen_univ hF.contDiffOn (x := x) (by
        intro k
        obtain ⟨α, hα0, hα⟩ := exists_solution_of_bounded_speed
          isOpen_univ hF.contDiffOn (p := x) (x := x) (R := C * ((k : ℝ) + 1))
          (T := (k : ℝ) + 1)
          (subset_univ _) hC (fun y _ => hbound y) (by positivity) (by simp)
        obtain ⟨ε, hε, β, hβ0, _, hβ⟩ := exists_open_solution_extension
          isOpen_univ hF.contDiffOn (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)
          (fun t ht => ⟨(hα t ht).1, (hα t ht).2.2⟩)
        exact ⟨ε, hε, β, hβ0.trans hα0, hβ, fun _ _ => mem_univ _⟩)
  exact ⟨δ, hδ, γ, hγ0, fun t ht => (hγ t ht).2⟩



theorem exists_global_solution_of_bounded_speed
    {F : E → E} (hF : ContDiff ℝ ∞ F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖F x‖ ≤ C) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (F (γ t)) t := by
  obtain ⟨δ, hδ, α, hα0, hα⟩ :=
    exists_forward_solution_of_bounded_speed hF hC hbound x
  obtain ⟨ε, hε, β, hβ0, hβ⟩ :=
    exists_forward_solution_of_bounded_speed hF.neg hC (by simpa using hbound) x
  have hβrev : ∀ t ∈ Iio ε, HasDerivAt (fun s => β (-s))
      (F (β (-t))) t := by
    intro t ht
    change t < ε at ht
    have hnt : -t ∈ Ioi (-ε) := by
      change -ε < -t
      exact neg_lt_neg ht
    have hd := (hβ (-t) hnt).scomp t
      (hasDerivAt_neg t)
    simpa only [Function.comp_def, neg_smul, one_smul, neg_neg] using hd
  obtain ⟨γ, hγα, hγβ, hγ⟩ := exists_gluing_of_solutions (U := univ)
    isOpen_univ hF.contDiffOn isOpen_Ioi isOpen_Iio (convex_Ioi _) (convex_Iio _)
    (fun t ht => ⟨mem_univ _, hα t ht⟩)
    (fun t ht => ⟨mem_univ _, hβrev t ht⟩)
    (a := 0) ⟨by change -δ < 0; linarith, hε⟩ (by simp [hα0, hβ0])
  refine ⟨γ, (hγα (by change -δ < 0; linarith)).trans hα0, fun t => ?_⟩
  apply (hγ t ?_).2
  change -δ < t ∨ t < ε
  rcases lt_or_ge (-δ) t with ht | ht
  · exact Or.inl ht
  · exact Or.inr (lt_of_le_of_lt ht (by linarith))


theorem exists_global_solution_of_eq_const_off_compact
    {F : E → E} (hF : ContDiff ℝ ∞ F) {K : Set E} (hK : IsCompact K)
    {v : E} (hfix : ∀ x, x ∉ K → F x = v) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (F (γ t)) t := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hF.continuous.continuousOn
  apply exists_global_solution_of_bounded_speed hF
    (C := max B ‖v‖) ((norm_nonneg v).trans (le_max_right _ _)) _ x
  intro y
  by_cases hy : y ∈ K
  · exact (hB y hy).trans (le_max_left _ _)
  · rw [hfix y hy]
    exact le_max_right _ _

end Poincare.ODE
