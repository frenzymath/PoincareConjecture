import PoincareConjecture.Proofs.M35.RadialGauge.RadialNormJets
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas











set_option autoImplicit false

open Set
open scoped ContDiff BigOperators

namespace PoincareConjecture.M35.RadialGauge

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem iteratedFDeriv_comp_nonzero_smul (f : E → F) {R : ℝ} (hR : R ≠ 0)
    (j : ℕ) (x : E) :
    iteratedFDeriv ℝ j (fun y => f (R • y)) x =
      R ^ j • iteratedFDeriv ℝ j f (R • x) := by
  let L : E ≃L[ℝ] E :=
    (LinearEquiv.smulOfUnit (Units.mk0 R hR) : E ≃ₗ[ℝ] E).toContinuousLinearEquiv
  have hL (y : E) : L y = R • y := rfl
  have h := L.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (L x)) j
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h
  change iteratedFDeriv ℝ j (f ∘ L) x = _
  rw [h]
  ext v
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, hL, smul_apply,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (iteratedFDeriv ℝ j f (R • x)).map_smul_univ (fun _ => R) v

end General

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]



theorem norm_exterior_jet_bounds (k : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i, 1 ≤ i → i ≤ k → ∀ x : E, 1 ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ i (fun y : E => ‖y‖) x‖ ≤ D := by
  obtain ⟨D, hD, hDb⟩ := norm_unit_sphere_jet_bounds (E := E) k
  refine ⟨D, hD, ?_⟩
  intro i hi hik x hx
  let R := ‖x‖
  let z := R⁻¹ • x
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hx
  have hz : ‖z‖ = 1 := by
    simp only [z, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    exact inv_mul_cancel₀ hR.ne'
  have hRz : R • z = x := by
    dsimp only [z]
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have hz0 : z ≠ 0 := by
    intro heq
    simp only [heq, norm_zero, zero_ne_one] at hz
  have hscale := iteratedFDeriv_comp_nonzero_smul (fun y : E => ‖y‖) hR.ne' i z
  have heq : (fun y : E => ‖R • y‖) = fun y => R • ‖y‖ := by
    funext y
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hR, smul_eq_mul]
  have hnorm : ContDiffAt ℝ i (fun y : E => ‖y‖) z :=
    (contDiffAt_id.norm ℝ hz0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl i)
  rw [heq, iteratedFDeriv_const_smul_apply' (a := R) hnorm, hRz] at hscale
  have hn := congrArg norm hscale
  simp only [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos hR] at hn
  have hp : R ≤ R ^ i := le_self_pow₀ hx (by omega)
  have hl : R * ‖iteratedFDeriv ℝ i (fun y : E => ‖y‖) x‖ ≤ R * D := by
    apply (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans
    rw [← hn]
    exact mul_le_mul_of_nonneg_left (hDb i hik z hz) hR.le
  exact (mul_le_mul_iff_right₀ hR).mp hl



theorem radial_exterior_weighted_jets {A : Type*} {f : A → ℝ → ℝ} {N : ℕ}
    (hf : ∀ a, ContDiffOn ℝ ∞ (f a) (Ioi 0))
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      (1 + r) ^ N * |iteratedDeriv j (f a) r| ≤ C) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ∀ x : E, 1 ≤ ‖x‖ →
      (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ k (fun y : E => f a ‖y‖) x‖ ≤ C := by
  classical
  intro k
  obtain ⟨D, hD, hDb⟩ := norm_exterior_jet_bounds (E := E) k
  choose B hB0 hB using hb
  let C := ∑ i ∈ Finset.range (k + 1), B i
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => hB0 i)
  refine ⟨(k.factorial : ℝ) * C * D ^ k, by positivity, ?_⟩
  intro a x hx
  let S := ({0} : Set E)ᶜ
  have hS : IsOpen S := isClosed_singleton.isOpen_compl
  have hpos : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
  have hxS : x ∈ S := norm_pos_iff.mp hpos
  have hn : ContDiffOn ℝ ∞ (fun y : E => ‖y‖) S :=
    fun y hy => (contDiffAt_id.norm ℝ (show y ≠ 0 from hy)).contDiffWithinAt
  have hw : 0 < (1 + ‖x‖) ^ N := pow_pos (by positivity) N
  have houter (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDerivWithin ℝ i (f a) (Ioi 0) ‖x‖‖ ≤ C / (1 + ‖x‖) ^ N := by
    rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi hpos,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    apply (le_div_iff₀ hw).mpr
    have hBi : B i ≤ C := Finset.single_le_sum (fun j _ => hB0 j)
      (show i ∈ Finset.range (k + 1) by
        simpa only [Finset.mem_range] using Nat.lt_succ_of_le hi)
    simpa only [mul_comm] using (hB i a ‖x‖ hx).trans hBi
  have hinner (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
      ‖iteratedFDerivWithin ℝ i (fun y : E => ‖y‖) S x‖ ≤ D ^ i := by
    rw [iteratedFDerivWithin_of_isOpen i hS hxS]
    exact (hDb i hi hik x hx).trans (le_self_pow₀ hD (by omega))
  have hcomp := norm_iteratedFDerivWithin_comp_le (hf a) hn
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl k) isOpen_Ioi.uniqueDiffOn hS.uniqueDiffOn
    (fun y hy => norm_pos_iff.mpr hy) hxS houter hinner
  rw [iteratedFDerivWithin_of_isOpen k hS hxS] at hcomp
  have hmul := mul_le_mul_of_nonneg_left hcomp hw.le
  have heq : (1 + ‖x‖) ^ N *
      ((k.factorial : ℝ) * (C / (1 + ‖x‖) ^ N) * D ^ k) =
      (k.factorial : ℝ) * C * D ^ k := by field_simp
  exact hmul.trans_eq heq

end Inner

end PoincareConjecture.M35.RadialGauge
