import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Minimizer.Weak.Hessian

/-!
# Iterating the near-Laplacian comparison

The harmonic comparison gives a contraction at a fixed radius ratio,
with a forcing error of order radius. The iteration retains a constant
depending only on the original energy and forcing bound. Source:
Sacks-Uhlenbeck Theorems 4.4-4.7, printed pp. 16-18; the local regularity
argument in `reports/weak-alpha-bootstrap.md`, Section 2.
-/

set_option autoImplicit false

open Set

noncomputable section

namespace PoincareMT.M60

/-- The harmonic and perturbation constants determine one smallness
threshold before the solution and before any prolonged jet. Source:
SU 4.4-4.7, near-Laplacian comparison. -/
theorem suComparison_smallness {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ q δ : ℝ, 0 < q ∧ q ≤ 1 / 4 ∧ 0 < δ ∧
      ∀ d : ℝ, 0 ≤ d → d ≤ δ → A * (q ^ 2) ^ 2 + B * d ^ 2 ≤ q / 2 := by
  let q := min (1 / 4 : ℝ) (1 / (4 * (A + 1)))
  have hq : 0 < q := lt_min (by norm_num) (by positivity)
  have hq1 : q ≤ 1 / 4 := min_le_left _ _
  have hqA : 4 * (A + 1) * q ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (A + 1))).mp
      (min_le_right (1 / 4 : ℝ) (1 / (4 * (A + 1))))
    nlinarith
  have hq2 : q ^ 2 ≤ 1 := by nlinarith
  have hq3 : q ^ 3 ≤ q := by
    have h := mul_le_mul_of_nonneg_left hq2 hq.le
    nlinarith
  have hAq3 : A * q ^ 3 ≤ 1 / 4 := by
    have h := mul_le_mul_of_nonneg_left hq3 hA
    nlinarith
  have hAq4 : A * (q ^ 2) ^ 2 ≤ q / 4 := by
    have h := mul_le_mul_of_nonneg_left hAq3 hq.le
    nlinarith
  let δ := Real.sqrt (q / (4 * (B + 1)))
  have hδ : 0 < δ := Real.sqrt_pos.2 (by positivity)
  have hδsq : δ ^ 2 = q / (4 * (B + 1)) := Real.sq_sqrt (by positivity)
  have hBδ : B * δ ^ 2 ≤ q / 4 := by
    rw [hδsq, ← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (B + 1))).mpr
    nlinarith
  refine ⟨q, δ, hq, hq1, hδ, ?_⟩
  intro d hd hdδ
  have hdsq := (sq_le_sq₀ hd hδ.le).mpr hdδ
  have h := mul_le_mul_of_nonneg_left hdsq hB
  linarith

/-- A quadratic radius contraction and a linear forcing error imply
square-root energy decay at every intermediate radius. The contraction
is chosen before the energy function. Source: SU 4.4-4.7, comparison
iteration for the local derivative modulus. -/
theorem suEnergy_sqrt_decay {q F : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hF : 0 ≤ F) {E : ℝ → ℝ} (hE : 0 ≤ E 1)
    (hmono : MonotoneOn E (Ioc 0 1))
    (hstep : ∀ r ∈ Ioc (0 : ℝ) 1, E (q ^ 2 * r) ≤ q / 2 * E r + F * r) :
    ∀ r ∈ Ioc (0 : ℝ) 1,
      E r ≤ ((E 1 + 2 * F / q) / q) * Real.sqrt r := by
  let K := E 1 + 2 * F / q
  have hK : 0 ≤ K := add_nonneg hE (div_nonneg (mul_nonneg (by norm_num) hF) hq.le)
  have hFK : F ≤ q / 2 * K := by
    dsimp only [K]
    have hcancel : q / 2 * (2 * F / q) = F := by field_simp
    rw [mul_add, hcancel]
    exact le_add_of_nonneg_left (mul_nonneg (by positivity) hE)
  have hq2 : q ^ 2 ≤ q := by nlinarith
  have hpow (k : ℕ) : E ((q ^ 2) ^ k) ≤ K * q ^ k := by
    induction k with
    | zero =>
      simpa only [pow_zero, mul_one] using le_add_of_nonneg_right
        (div_nonneg (mul_nonneg (by norm_num) hF) hq.le : 0 ≤ 2 * F / q)
    | succ k ih =>
      have hr : (q ^ 2) ^ k ∈ Ioc (0 : ℝ) 1 :=
        ⟨pow_pos (sq_pos_of_pos hq) _, pow_le_one₀ (sq_nonneg q) (by nlinarith)⟩
      have hqp : (q ^ 2) ^ k ≤ q ^ k := pow_le_pow_left₀ (sq_nonneg q) hq2 k
      calc
        E ((q ^ 2) ^ (k + 1)) = E (q ^ 2 * (q ^ 2) ^ k) :=
          congrArg E (pow_succ' _ _)
        _ ≤ q / 2 * E ((q ^ 2) ^ k) + F * (q ^ 2) ^ k := hstep _ hr
        _ ≤ q / 2 * (K * q ^ k) + F * q ^ k :=
          add_le_add (mul_le_mul_of_nonneg_left ih (by positivity))
            (mul_le_mul_of_nonneg_left hqp hF)
        _ ≤ q / 2 * (K * q ^ k) + (q / 2 * K) * q ^ k :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right hFK (pow_nonneg hq.le _))
        _ = K * q ^ (k + 1) := by rw [pow_succ]; ring
  intro r hr
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near_of_lt_one hr.1 hr.2
    (sq_pos_of_pos hq) (by nlinarith : q ^ 2 < 1)
  have hkin : (q ^ 2) ^ k ∈ Ioc (0 : ℝ) 1 :=
    ⟨pow_pos (sq_pos_of_pos hq) _, pow_le_one₀ (sq_nonneg q) (by nlinarith)⟩
  have hs : q ^ (k + 1) < Real.sqrt r := by
    have he : (q ^ (k + 1)) ^ 2 = (q ^ 2) ^ (k + 1) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    have h := Real.sqrt_lt_sqrt (sq_nonneg (q ^ (k + 1))) (he.trans_lt hklo)
    rwa [Real.sqrt_sq (pow_nonneg hq.le _)] at h
  have hqp : q ^ k ≤ Real.sqrt r / q := by
    apply (le_div_iff₀ hq).mpr
    simpa only [pow_succ, mul_comm] using hs.le
  calc
    E r ≤ E ((q ^ 2) ^ k) := hmono hr hkin hkhi
    _ ≤ K * q ^ k := hpow k
    _ ≤ K * (Real.sqrt r / q) := mul_le_mul_of_nonneg_left hqp hK
    _ = _ := by dsimp only [K]; ring

end PoincareMT.M60

end
