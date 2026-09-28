import PoincareConjecture.Proofs.M35.RadialGauge.RadialExteriorJets
import PoincareConjecture.Proofs.M35.RadialGauge.EvenRadialCompactJets

set_option autoImplicit false

open Set
open scoped ContDiff BigOperators

namespace PoincareConjecture.M35.RadialGauge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem even_radial_family_weighted_jets {A : Type*} {f : A → ℝ → ℝ} {N : ℕ}
    (hf : ∀ a, ContDiff ℝ ∞ (f a)) (he : ∀ a, Function.Even (f a))
    (hnear : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, |r| ≤ 1 →
      |iteratedDeriv j (f a) r| ≤ C)
    (hfar : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      (1 + r) ^ N * |iteratedDeriv j (f a) r| ≤ C) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ∀ x : E,
      (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j (fun y : E => f a ‖y‖) x‖ ≤ C := by
  intro j
  obtain ⟨C, hC, hCb⟩ :=
    even_radial_compact_jets_bounded (E := E) zero_le_one hf he hnear j
  obtain ⟨D, hD, hDb⟩ :=
    radial_exterior_weighted_jets (E := E) (fun a => (hf a).contDiffOn) hfar j
  refine ⟨(2 : ℝ) ^ N * C + D, by positivity, ?_⟩
  intro a x
  by_cases hx : 1 ≤ ‖x‖
  · exact (hDb a x hx).trans (le_add_of_nonneg_left (by positivity))
  · have hx1 : ‖x‖ ≤ 1 := le_of_lt (lt_of_not_ge hx)
    have hm := mul_le_mul
      (pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖x‖) (by linarith only [hx1]) N)
      (hCb a x hx1) (norm_nonneg _) (by positivity : 0 ≤ (2 : ℝ) ^ N)
    exact hm.trans (le_add_of_nonneg_right hD)

omit [FiniteDimensional ℝ E] in
private theorem identity_jet_bound (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y : E => y) x‖ ≤ 1 + ‖x‖ := by
  cases j with
  | zero => simpa only [norm_iteratedFDeriv_zero] using le_add_of_nonneg_left zero_le_one
  | succ j =>
      rw [← norm_iteratedFDeriv_fderiv]
      have hid : fderiv ℝ (fun y : E => y) = fun _ => ContinuousLinearMap.id ℝ E :=
        funext (fun y => (hasFDerivAt_id y).fderiv)
      rw [hid]
      cases j with
      | zero =>
          rw [norm_iteratedFDeriv_zero]
          exact ContinuousLinearMap.norm_id_le.trans (le_add_of_nonneg_right (norm_nonneg x))
      | succ j =>
          simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
          positivity

omit [FiniteDimensional ℝ E] in

theorem radial_vector_jets_bounded {A : Type*} {f : A → ℝ → ℝ}
    (hf : ∀ a, ContDiff ℝ ∞ (f a)) (he : ∀ a, Function.Even (f a))
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ∀ x : E,
      (1 + ‖x‖) * ‖iteratedFDeriv ℝ j (fun y : E => f a ‖y‖) x‖ ≤ C) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ∀ x : E,
      ‖iteratedFDeriv ℝ j (fun y : E => f a ‖y‖ • y) x‖ ≤ C := by
  classical
  choose B hB0 hB using hb
  intro j
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i,
    Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hB0 i)), ?_⟩
  intro a x
  apply (norm_iteratedFDeriv_smul_le (g := fun y : E => y)
    (SmoothRadial.contDiff_even_norm (hf a) (he a))
    (contDiff_id : ContDiff ℝ ∞ (fun y : E => y)) x
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).trans
  apply Finset.sum_le_sum
  intro i _
  have hm := mul_le_mul_of_nonneg_left (identity_jet_bound (j - i) x)
    (norm_nonneg (iteratedFDeriv ℝ i (fun y : E => f a ‖y‖) x))
  have hbound : ‖iteratedFDeriv ℝ i (fun y : E => f a ‖y‖) x‖ *
      ‖iteratedFDeriv ℝ (j - i) (fun y : E => y) x‖ ≤ B i := by
    apply hm.trans
    simpa only [mul_comm] using hB i a x
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg (j.choose i))

end PoincareConjecture.M35.RadialGauge
