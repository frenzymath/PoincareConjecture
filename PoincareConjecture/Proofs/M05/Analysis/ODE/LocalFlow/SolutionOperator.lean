/-
Provenance and modification notice (recorded 2026-09-29).
Notices for the adapted portions:
Copyright 2026 The DifferentialGeometry contributors
Source: https://github.com/qinz1yang/differential-geometry
DifferentialGeometry/Analysis/ODE/Flow/SolutionOperator.lean
Comparison revision: 1b535dd102b94cc42b107cca27059687888f08b3.
Modifications: Imports, module paths, and namespaces were adapted to this PoincareConjecture
development.
License: Apache-2.0; see LICENSES/Apache-2.0.txt and NOTICE.
See MODIFICATIONS.md for the reviewed file mapping and scope of this notice.
-/

import PoincareConjecture.Proofs.M05.Analysis.ODE.LocalFlow.HigherRegularity.VariationalLinearMapSmoothness
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal ContDiff

namespace Poincare.ODE.LocalFlow

section ShortIntervalExistence

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem exists_linearODE_solution_of_short
    {A : ℝ → (G →L[ℝ] G)} {h₀ : ℝ} {T M : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn A (Icc (h₀ - T) (h₀ + T)))
    (hA_bd : ∀ t ∈ Icc (h₀ - T) (h₀ + T), ‖A t‖ ≤ M)
    (Z₀ : G) :
    ∃ Z : ℝ → G, Z h₀ = Z₀ ∧
      ∀ t ∈ Icc (h₀ - T) (h₀ + T), HasDerivWithinAt Z (A t (Z t))
        (Icc (h₀ - T) (h₀ + T)) t := by
  set v : ℝ → G → G := fun t y => A t y with hv_def
  set r₀ : ℝ := ‖Z₀‖ with hr₀_def
  have hr₀_nn : 0 ≤ r₀ := norm_nonneg _
  have h1mMT_pos : 0 < 1 - M * T := by linarith
  set a₀ : ℝ := (r₀ + 1) / (1 - M * T) with ha₀_def
  have ha₀_pos : 0 < a₀ := div_pos (by linarith [hr₀_nn]) h1mMT_pos
  have ha₀_nn : 0 ≤ a₀ := le_of_lt ha₀_pos
  have hMaT_le : M * a₀ * T ≤ a₀ - r₀ := by
    have hkey : a₀ * (1 - M * T) = r₀ + 1 := by
      rw [ha₀_def]; field_simp
    have h1 : a₀ - M * a₀ * T = r₀ + 1 := by
      have : a₀ - M * a₀ * T = a₀ * (1 - M * T) := by ring
      rw [this, hkey]
    linarith
  let tmin : ℝ := h₀ - T
  let tmax : ℝ := h₀ + T
  have htmin_le_t₀ : tmin ≤ h₀ := by change h₀ - T ≤ h₀; linarith
  have ht₀_le_tmax : h₀ ≤ tmax := by change h₀ ≤ h₀ + T; linarith
  let t₀Icc : Icc tmin tmax := ⟨h₀, ⟨htmin_le_t₀, ht₀_le_tmax⟩⟩
  let aN : ℝ≥0 := NNReal.mk a₀ ha₀_nn
  let rN : ℝ≥0 := NNReal.mk r₀ hr₀_nn
  let LN : ℝ≥0 := NNReal.mk (M * a₀) (mul_nonneg hM ha₀_nn)
  let KN : ℝ≥0 := NNReal.mk M hM
  have hpl : IsPicardLindelof v t₀Icc (0 : G) aN rN LN KN := by
    refine
    { lipschitzOnWith := ?_,
      continuousOn := ?_,
      norm_le := ?_,
      mul_max_le := ?_ }
    · intro t ht
      have hAτ_bd : ‖A t‖ ≤ M := hA_bd t ht
      have hlip : LipschitzWith KN (A t) := (A t).lipschitzWith_of_opNorm_le hAτ_bd
      exact hlip.lipschitzOnWith (s := closedBall (0 : G) aN)
    · intro y _
      have happly : Continuous (fun B : G →L[ℝ] G => B y) :=
        (ContinuousLinearMap.apply ℝ G y).continuous
      exact happly.comp_continuousOn hA_cont
    · intro t ht y hy
      have hAt_bd : ‖A t‖ ≤ M := hA_bd t ht
      have hy_norm : ‖y‖ ≤ a₀ := by
        have hy' : ‖y‖ ≤ (aN : ℝ) := by
          simpa only [mem_closedBall_zero_iff] using hy
        simpa only [aN, NNReal.coe_mk] using hy'
      change ‖v t y‖ ≤ (LN : ℝ)
      calc ‖v t y‖ = ‖A t y‖ := rfl
        _ ≤ ‖A t‖ * ‖y‖ := (A t).le_opNorm y
        _ ≤ M * a₀ := mul_le_mul hAt_bd hy_norm (norm_nonneg _) hM
    · change (LN : ℝ) * max (tmax - h₀) (h₀ - tmin) ≤ (aN : ℝ) - (rN : ℝ)
      have hmax_eq : max (tmax - h₀) (h₀ - tmin) = T := by
        have h1 : tmax - h₀ = T := by change (h₀ + T) - h₀ = T; ring
        have h2 : h₀ - tmin = T := by change h₀ - (h₀ - T) = T; ring
        rw [h1, h2]; exact max_self _
      rw [hmax_eq]
      change M * a₀ * T ≤ a₀ - r₀
      exact hMaT_le
  have hZ₀_mem : Z₀ ∈ closedBall (0 : G) rN := by
    rw [mem_closedBall_zero_iff]; change ‖Z₀‖ ≤ r₀; rfl
  obtain ⟨Z, hZ_init, hZ_deriv⟩ :=
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt hZ₀_mem
  exact ⟨Z, hZ_init, hZ_deriv⟩

end ShortIntervalExistence

section Uniqueness

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem linearODE_unique_on_Ioo
    {A : ℝ → (G →L[ℝ] G)} {a b h₀ : ℝ}
    (ht₀ : h₀ ∈ Ioo a b)
    (hA_cont : ContinuousOn A (Ioo a b))
    {Z₁ Z₂ : ℝ → G}
    (hZ₁ : ∀ t ∈ Ioo a b, HasDerivAt Z₁ (A t (Z₁ t)) t)
    (hZ₂ : ∀ t ∈ Ioo a b, HasDerivAt Z₂ (A t (Z₂ t)) t)
    (heq : Z₁ h₀ = Z₂ h₀) :
    EqOn Z₁ Z₂ (Ioo a b) := by
  intro t ht
  let v : ℝ → G → G := fun t y => A t y
  set a' := (a + min t h₀) / 2 with ha'
  set b' := (b + max t h₀) / 2 with hb'
  have hmin_lt : a < min t h₀ := lt_min ht.1 ht₀.1
  have hmax_lt : max t h₀ < b := max_lt ht.2 ht₀.2
  have hmin_le_t : min t h₀ ≤ t := min_le_left _ _
  have hmin_le_t₀ : min t h₀ ≤ h₀ := min_le_right _ _
  have ht_le_max : t ≤ max t h₀ := le_max_left _ _
  have ht₀_le_max : h₀ ≤ max t h₀ := le_max_right _ _
  have ha'_lt_min : a' < min t h₀ := by rw [ha']; linarith
  have ha_lt_a' : a < a' := by rw [ha']; linarith
  have hmax_lt_b' : max t h₀ < b' := by rw [hb']; linarith
  have hb'_lt_b : b' < b := by rw [hb']; linarith
  have hsub : Ioo a' b' ⊆ Ioo a b := fun s hs =>
    ⟨lt_trans ha_lt_a' hs.1, lt_trans hs.2 hb'_lt_b⟩
  have ht_mem' : t ∈ Ioo a' b' :=
    ⟨lt_of_lt_of_le ha'_lt_min hmin_le_t, lt_of_le_of_lt ht_le_max hmax_lt_b'⟩
  have ht₀_mem' : h₀ ∈ Ioo a' b' :=
    ⟨lt_of_lt_of_le ha'_lt_min hmin_le_t₀, lt_of_le_of_lt ht₀_le_max hmax_lt_b'⟩
  have hab_le : a' ≤ b' := le_of_lt (lt_trans ha'_lt_min (lt_of_le_of_lt hmin_le_t
    (lt_of_lt_of_le ht_mem'.2 (le_refl _))))
  have hIcc_sub : Icc a' b' ⊆ Ioo a b := fun s hs =>
    ⟨lt_of_lt_of_le ha_lt_a' hs.1, lt_of_le_of_lt hs.2 hb'_lt_b⟩
  have hbd : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Icc a' b', ‖A τ‖ ≤ M := by
    have hcont' : ContinuousOn A (Icc a' b') := hA_cont.mono hIcc_sub
    have hcont_norm : ContinuousOn (fun τ => ‖A τ‖) (Icc a' b') :=
      continuous_norm.comp_continuousOn hcont'
    have hcpt : IsCompact (Icc a' b') := isCompact_Icc
    have hne : (Icc a' b').Nonempty := ⟨a', left_mem_Icc.mpr hab_le⟩
    rcases hcpt.exists_isMaxOn hne hcont_norm with ⟨τ₁, _, hτ₁_max⟩
    exact ⟨‖A τ₁‖, norm_nonneg _, fun τ hτ => hτ₁_max hτ⟩
  obtain ⟨M, hM_nn, hMbd⟩ := hbd
  let K : ℝ≥0 := ⟨M, hM_nn⟩
  have hv_lip : ∀ τ ∈ Ioo a' b', LipschitzOnWith K (v τ) univ := by
    intro τ hτ
    have hlip : LipschitzWith K (A τ) :=
      (A τ).lipschitzWith_of_opNorm_le (hMbd τ (Ioo_subset_Icc_self hτ))
    exact (LipschitzWith.lipschitzOnWith (s := (univ : Set G)) hlip)
  exact (ODE_solution_unique_of_mem_Ioo (v := v) (s := fun _ => univ) (K := K)
    hv_lip ht₀_mem'
    (fun τ hτ => ⟨hZ₁ τ (hsub hτ), mem_univ _⟩)
    (fun τ hτ => ⟨hZ₂ τ (hsub hτ), mem_univ _⟩)
    heq) ht_mem'

end Uniqueness

section SolutionOperator

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

def HasLinearODESolution
    (A : F → ℝ → (G →L[ℝ] G)) (a b h₀ : ℝ) (Z₀ : F → G) (x : F) : Prop :=
  ∃ Z : ℝ → G, Z h₀ = Z₀ x ∧ ∀ t ∈ Ioo a b, HasDerivAt Z (A x t (Z t)) t

noncomputable def linearODESolution
    (A : F → ℝ → (G →L[ℝ] G)) (a b h₀ : ℝ) (Z₀ : F → G) :
    F → ℝ → G := by
  classical
  exact fun x =>
    if h : HasLinearODESolution A a b h₀ Z₀ x then
      Classical.choose h
    else
      fun _ => Z₀ x

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace G] in
@[simp]
theorem linearODESolution_init
    (A : F → ℝ → (G →L[ℝ] G)) (a b h₀ : ℝ) (Z₀ : F → G) (x : F) :
    linearODESolution A a b h₀ Z₀ x h₀ = Z₀ x := by
  unfold linearODESolution
  by_cases h : HasLinearODESolution A a b h₀ Z₀ x
  · simp only [dif_pos h]
    exact (Classical.choose_spec h).1
  · simp only [dif_neg h]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace G] in
theorem linearODESolution_hasDerivAt_of_hasSolution
    (A : F → ℝ → (G →L[ℝ] G)) (a b h₀ : ℝ) (Z₀ : F → G)
    {x : F} (hx : HasLinearODESolution A a b h₀ Z₀ x) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (linearODESolution A a b h₀ Z₀ x ·)
      (A x t (linearODESolution A a b h₀ Z₀ x t)) t := by
  have hZ_eq : linearODESolution A a b h₀ Z₀ x = Classical.choose hx := by
    unfold linearODESolution
    simp only [dif_pos hx]
  rw [hZ_eq]
  exact (Classical.choose_spec hx).2 t ht

end SolutionOperator

end Poincare.ODE.LocalFlow

end
