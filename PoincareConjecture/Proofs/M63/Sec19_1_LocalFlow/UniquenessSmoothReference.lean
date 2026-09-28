import PoincareConjecture.Proofs.M63.Mathlib.PeriodicSmoothApproximation
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact










set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M63





theorem exists_periodic_smooth_normalGraph_reference
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {P : ℝ} (hP : 0 < P) {c : ℝ → E}
    (hc : ContDiff ℝ 2 c) (hp : Function.Periodic c P)
    (himm : ∀ x, deriv c x ≠ 0) :
    ∃ (r : ℝ → E) (m M B rho eps eta : ℝ),
      ContDiff ℝ ∞ r ∧ Function.Periodic r P ∧
      0 < m ∧ 0 < M ∧ 0 < B ∧ 0 < rho ∧ 0 < eps ∧ 0 < eta ∧
      (∀ x, m ≤ ‖deriv r x‖) ∧ (∀ x, ‖deriv r x‖ ≤ M) ∧
      (∀ x, ‖deriv (deriv r) x‖ ≤ B) ∧
      2 * B * (eps + M * rho) ≤ m ^ 2 ∧
      4 * eps * M ≤ m ^ 2 * rho ∧
      2 * M * (eta + B * rho) ≤ m ^ 2 ∧
      (∀ x, ‖c x - r x‖ < eps / 2) ∧
      ∀ x, ‖deriv c x - deriv r x‖ < eta / 2 := by
  have hc₁ : ContDiff ℝ 1 (deriv c) := hc.deriv' (n := 1)
  have hp₁ := hp.deriv_of_differentiable (hc.differentiable (by norm_num))
  have hp₂ := hp₁.deriv_of_differentiable (hc₁.differentiable (by norm_num))
  have hK₁ := hp₁.compact_of_continuous hP.ne' hc₁.continuous
  have hK₂ := hp₂.compact_of_continuous hP.ne' hc₁.continuous_deriv_one
  obtain ⟨v, ⟨x₀, rfl⟩, hmin⟩ := hK₁.exists_isMinOn
    (range_nonempty (deriv c)) continuous_norm.continuousOn
  let m₀ := ‖deriv c x₀‖
  have hm₀ : 0 < m₀ := norm_pos_iff.mpr (himm x₀)
  have hlower (x : ℝ) : m₀ ≤ ‖deriv c x‖ := hmin (mem_range_self x)
  obtain ⟨M₀, hM₀bound⟩ := hK₁.exists_bound_of_continuousOn continuousOn_id
  obtain ⟨B₀, hB₀bound⟩ := hK₂.exists_bound_of_continuousOn continuousOn_id
  have hM₀ : 0 ≤ M₀ := (norm_nonneg (deriv c 0)).trans
    (hM₀bound (deriv c 0) (mem_range_self 0))
  have hB₀ : 0 ≤ B₀ := (norm_nonneg (deriv (deriv c) 0)).trans
    (hB₀bound (deriv (deriv c) 0) (mem_range_self 0))
  let m := m₀ / 2
  let M := M₀ + 1
  let B := B₀ + 1
  let rho := m ^ 2 / (8 * B * M)
  let eps := min (m ^ 2 / (8 * B)) (m ^ 2 * rho / (8 * M))
  let eta := m ^ 2 / (8 * M)
  have hm : 0 < m := half_pos hm₀
  have hM : 0 < M := by dsimp only [M]; linarith
  have hB : 0 < B := by dsimp only [B]; linarith
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hMrho : M * rho = m ^ 2 / (8 * B) := by
    dsimp only [rho]
    field_simp
  have hBrho : B * rho = m ^ 2 / (8 * M) := by
    dsimp only [rho]
    field_simp
  have hsmall : 2 * B * (eps + M * rho) ≤ m ^ 2 := by
    calc
      2 * B * (eps + M * rho) ≤
          2 * B * (m ^ 2 / (8 * B) + m ^ 2 / (8 * B)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (min_le_left _ _) hMrho.le) (by positivity)
      _ = m ^ 2 / 2 := by field_simp; ring
      _ ≤ m ^ 2 := by nlinarith [sq_nonneg m]
  have hmargin : 4 * eps * M ≤ m ^ 2 * rho := by
    calc
      4 * eps * M ≤ 4 * (m ^ 2 * rho / (8 * M)) * M :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)) hM.le
      _ = m ^ 2 * rho / 2 := by field_simp; ring
      _ ≤ m ^ 2 * rho := by nlinarith [mul_nonneg (sq_nonneg m) hrho.le]
  have htrans : 2 * M * (eta + B * rho) ≤ m ^ 2 := by
    rw [hBrho]
    change 2 * M * (m ^ 2 / (8 * M) + m ^ 2 / (8 * M)) ≤ m ^ 2
    have heq : 2 * M * (m ^ 2 / (8 * M) + m ^ 2 / (8 * M)) = m ^ 2 / 2 := by
      field_simp
      ring
    rw [heq]
    nlinarith [sq_nonneg m]
  let tol := min (eps / 2) (min (eta / 2) (min (m₀ / 2) (1 / 2)))
  have htol : 0 < tol := by dsimp only [tol]; positivity
  have htol_eps : tol ≤ eps / 2 := min_le_left _ _
  have htol_eta : tol ≤ eta / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have htol_m : tol ≤ m₀ / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have htol_one : tol ≤ 1 / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨r, hr, hrper, happ⟩ := exists_periodic_smooth_C2_approximation hP hc hp htol
  refine ⟨r, m, M, B, rho, eps, eta, hr, hrper, hm, hM, hB, hrho, heps, heta,
    ?_, ?_, ?_, hsmall, hmargin, htrans, ?_, ?_⟩
  · intro x
    have hdiff := (happ x).2.1.trans_le htol_m
    have hreverse := norm_sub_norm_le (deriv c x) (deriv r x)
    rw [norm_sub_rev] at hreverse
    have hlow := hlower x
    dsimp only [m]
    linarith
  · intro x
    have hdiff := (happ x).2.1.trans_le htol_one
    have hbound : ‖deriv c x‖ ≤ M₀ := hM₀bound (deriv c x) (mem_range_self x)
    have htriangle := norm_add_le (deriv r x - deriv c x) (deriv c x)
    rw [sub_add_cancel] at htriangle
    dsimp only [M]
    linarith
  · intro x
    have hdiff := (happ x).2.2.trans_le htol_one
    have hbound : ‖deriv (deriv c) x‖ ≤ B₀ :=
      hB₀bound (deriv (deriv c) x) (mem_range_self x)
    have htriangle := norm_add_le
      (deriv (deriv r) x - deriv (deriv c) x) (deriv (deriv c) x)
    rw [sub_add_cancel] at htriangle
    dsimp only [B]
    linarith
  · intro x
    rw [norm_sub_rev]
    exact (happ x).1.trans_le htol_eps
  · intro x
    rw [norm_sub_rev]
    exact (happ x).2.1.trans_le htol_eta

end PoincareConjecture.M63
