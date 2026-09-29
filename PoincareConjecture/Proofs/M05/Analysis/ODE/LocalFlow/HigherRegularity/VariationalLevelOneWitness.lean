/-
Provenance and modification notice (recorded 2026-09-29).
Notices for the adapted portions:
Copyright 2026 The DifferentialGeometry contributors
Source: https://github.com/qinz1yang/differential-geometry
DifferentialGeometry/Analysis/ODE/Flow/HigherRegularity/VariationalLevelOneWitness.lean
Comparison revision: 1b535dd102b94cc42b107cca27059687888f08b3.
Modifications: Imports, module paths, and namespaces were adapted to this PoincareConjecture
development.
License: Apache-2.0; see LICENSES/Apache-2.0.txt and NOTICE.
See MODIFICATIONS.md for the reviewed file mapping and scope of this notice.
-/

import PoincareConjecture.Proofs.M05.Analysis.ODE.LocalFlow.HigherRegularity.VariationalCoproductDerivative

noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal

namespace Poincare.ODE.LocalFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

attribute [local instance] variationalAugmentedEndNormedAddCommGroup

section LevelOneFullWitness

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

theorem exists_isVariationalFlowProjection_one_of_C2
    [FiniteDimensional ℝ E]
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (ht₀_Ioo : t₀ ∈ Ioo tmin tmax)
    (hr_pos : (0 : ℝ) < (r : ℝ))
    (hf_C2 : ContDiffOn ℝ 2 (uncurry f) (Set.univ : Set (ℝ × E))) :
    ∃ (T : ℝ) (ρ : ℝ≥0) (_hT : 0 < T) (_hρ : 0 < (ρ : ℝ))
      (Y : E × ℝ → (E →L[ℝ] E)),
      IsVariationalFlowProjection hΦ T ρ Y 1 := by
  classical
  obtain ⟨R_aug, ε_aug, hR_aug_pos, hε_aug_pos, aΦ, T_final, ρ_finalN,
      hT_final_pos, hρ_final_pos, haΦ, h_Y_smooth⟩ :=
    exists_isLocalFlow_augmentedVectorField_and_contDiffOn_fromAugFlow_one_of_C2
      hf_C2 t₀ x₀
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (by decide : (1 : ℕ∞) ≤ 2)
    exact hf_C2.of_le h_le
  have hR_aug_R : (0 : ℝ) < (R_aug : ℝ) := by
    exact_mod_cast hR_aug_pos
  have ht₀_a_Ioo : t₀ ∈ Ioo (t₀ - ε_aug) (t₀ + ε_aug) :=
    ⟨by linarith, by linarith⟩
  obtain ⟨T_help, ρ_help, hT_help_pos, hρ_help_pos, h_help⟩ :=
    fderiv_Phi_eq_coprod_fromAugFlow_aux (Φ := Φ) hΦ hf_C1 ht₀_Ioo hr_pos haΦ ht₀_a_Ioo hR_aug_R
  set T_eff : ℝ := min T_final T_help with hT_eff_def
  have hT_eff_pos : 0 < T_eff := lt_min hT_final_pos hT_help_pos
  have hT_eff_le_final : T_eff ≤ T_final := min_le_left _ _
  have hT_eff_le_help : T_eff ≤ T_help := min_le_right _ _
  set ρ_eff : ℝ := min (ρ_finalN : ℝ) (ρ_help : ℝ) with hρ_eff_def
  have hρ_eff_pos : 0 < ρ_eff := lt_min hρ_final_pos hρ_help_pos
  set ρ_effN : ℝ≥0 := ⟨ρ_eff, le_of_lt hρ_eff_pos⟩
  have hρ_effN_eq : (ρ_effN : ℝ) = ρ_eff := rfl
  have hρ_eff_le_finalN : ρ_eff ≤ (ρ_finalN : ℝ) := min_le_left _ _
  have hρ_eff_le_help : ρ_eff ≤ (ρ_help : ℝ) := min_le_right _ _
  have hρ_effN_le_finalN : (ρ_effN : ℝ) ≤ (ρ_finalN : ℝ) := by
    rw [hρ_effN_eq]
    exact hρ_eff_le_finalN
  have hρ_effN_le_help : (ρ_effN : ℝ) ≤ (ρ_help : ℝ) := by
    rw [hρ_effN_eq]
    exact hρ_eff_le_help
  have h_eff_sub_smooth : (ball x₀ (ρ_effN : ℝ)) ×ˢ Ioo (t₀ - T_eff) (t₀ + T_eff)
      ⊆ (ball x₀ (ρ_finalN : ℝ)) ×ˢ Ioo (t₀ - T_final) (t₀ + T_final) := by
    refine Set.prod_mono ?_ ?_
    · intro y hy
      rw [mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy hρ_effN_le_finalN
    · intro s hs
      rcases hs with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩ <;> linarith
  have h_eff_sub_help : (ball x₀ (ρ_effN : ℝ)) ×ˢ Ioo (t₀ - T_eff) (t₀ + T_eff)
      ⊆ (ball x₀ (ρ_help : ℝ)) ×ˢ Ioo (t₀ - T_help) (t₀ + T_help) := by
    refine Set.prod_mono ?_ ?_
    · intro y hy
      rw [mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy hρ_effN_le_help
    · intro s hs
      rcases hs with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩ <;> linarith
  refine ⟨T_eff, ρ_effN, hT_eff_pos, hρ_eff_pos, fromAugFlow aΦ, ?_⟩
  refine { contDiffOn := h_Y_smooth.mono h_eff_sub_smooth, fderiv_eq := ?_ }
  intro q hq
  exact h_help q (h_eff_sub_help hq)

end LevelOneFullWitness

end Poincare.ODE.LocalFlow

end
