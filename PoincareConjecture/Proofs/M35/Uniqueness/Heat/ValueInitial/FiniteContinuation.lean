import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.PrincipalJoin

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat.ValueInitial

open SpectralHeatNative

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem principalValueHeat_zero (K : Set V) (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    (L : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletValue K)) (r : ℝ)
    (u₀ : PiLp 2 (fun _ : Fin m => dirichletValue K)) :
    PrincipalValueHeat K A L r 0 u₀ (fun _ => 0) (fun _ => u₀) := by
  refine ⟨MemLp.zero', rfl, continuousOn_const, ?_, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact False.elim (not_lt_of_ge ht.2 ht.1)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact False.elim (not_lt_of_ge ht.2 ht.1)
  · intro t ht w
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    simp only [intervalIntegral.integral_same, add_zero]

theorem exists_principal_value_heat_of_uniform_restart
    (K : Set V) (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    (L : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletValue K)) {a b τ : ℝ}
    (hab : a ≤ b) (hτ : 0 < τ)
    (hAc : ContinuousOn (fun t => principalFormOperator K (A t)) (Icc a b))
    (hLc : ContinuousOn L (Icc a b))
    (hsolve : ∀ r ∈ Icc a b, ∀ T ∈ Icc 0 τ, r + T ≤ b →
      ∀ u₀, ∃ v U, PrincipalValueHeat K A L r T u₀ v U)
    (u₀ : PiLp 2 (fun _ : Fin m => dirichletValue K)) :
    ∃ v U, PrincipalValueHeat K A L a (b - a) u₀ v U := by
  rcases eq_or_lt_of_le hab with hab | hab
  · subst b
    exact ⟨fun _ => 0, fun _ => u₀, by
      simpa only [sub_self] using principalValueHeat_zero K A L a u₀⟩
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / τ)
  have hNr : 0 < (N : ℝ) := (div_pos (sub_pos.mpr hab) hτ).trans hN
  let d := (b - a) / (N : ℝ)
  have hd : 0 < d := div_pos (sub_pos.mpr hab) hNr
  have hNd : (N : ℝ) * d = b - a := mul_div_cancel₀ _ hNr.ne'
  have hdτ : d ≤ τ := by
    apply (div_le_iff₀ hNr).mpr
    have h := (div_lt_iff₀ hτ).mp hN
    nlinarith only [h]
  have hsteps : ∀ k : ℕ, k ≤ N → ∃ v U, PrincipalValueHeat K A L a ((k : ℝ) * d) u₀ v U := by
    intro k
    induction k with
    | zero =>
        intro _
        exact ⟨fun _ => 0, fun _ => u₀, by
          simpa only [Nat.cast_zero, zero_mul] using principalValueHeat_zero K A L a u₀⟩
    | succ k ih =>
        intro hk
        have hk0 : 0 ≤ (k : ℝ) * d := mul_nonneg (Nat.cast_nonneg k) hd.le
        have hkend : a + ((k : ℝ) * d + d) ≤ b := by
          have hkn : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk
          have hmul := mul_le_mul_of_nonneg_right hkn hd.le
          rw [hNd] at hmul
          nlinarith only [hmul]
        have hkr : a + (k : ℝ) * d ∈ Icc a b := by
          constructor <;> linarith only [hk0, hkend, hd]
        obtain ⟨v₁, U₁, h₁⟩ := ih ((Nat.le_succ k).trans hk)
        obtain ⟨v₂, U₂, h₂⟩ := hsolve (a + (k : ℝ) * d) hkr d ⟨hd.le, hdτ⟩
          (by linarith only [hkend]) (U₁ ((k : ℝ) * d))
        have hshift : MapsTo (fun t : ℝ => a + t) (Icc 0 ((k : ℝ) * d + d)) (Icc a b) := by
          intro t ht
          constructor <;> linarith only [ht.1, ht.2, hkend]
        have hA' : ContinuousOn (fun t => principalFormOperator K (A (a + t)))
            (Icc 0 ((k : ℝ) * d + d)) :=
          hAc.comp (continuous_const.add continuous_id).continuousOn hshift
        have hL' : ContinuousOn (fun t => L (a + t)) (Icc 0 ((k : ℝ) * d + d)) :=
          hLc.comp (continuous_const.add continuous_id).continuousOn hshift
        have hj := principalValueHeat_join K A L hk0 hd.le hA' hL' h₁ h₂
        refine ⟨joinTime v₁ v₂ ((k : ℝ) * d), joinTime U₁ U₂ ((k : ℝ) * d), ?_⟩
        simpa only [Nat.cast_succ, add_mul, one_mul] using hj
  obtain ⟨v, U, h⟩ := hsteps N le_rfl
  exact ⟨v, U, by simpa only [hNd] using h⟩

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial
