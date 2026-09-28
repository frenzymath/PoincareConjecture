import PoincareConjecture.Proofs.M04.ShiBernsteinHeat








set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

noncomputable def shiShiftedReactionScale (l : ℕ) (Θ : ℝ) : ℝ :=
  Θ * (max 1 Θ) ^ l

private noncomputable def reaction (n m : ℕ) (N : ℕ → ℝ) : ℝ :=
  2 * (n : ℝ) * (curvatureReactionWeight m : ℝ) * N m *
    (∑ i ∈ Finset.range (m + 1), N i * N (m - i)) +
    2 * (m + 4 : ℕ) * (n : ℝ) ^ (m + 6) * N 0 * (N m) ^ 2

theorem shiShiftedReactionScale_nonneg (l : ℕ) {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    0 ≤ shiShiftedReactionScale l Θ := by
  unfold shiShiftedReactionScale
  positivity

private theorem shifted_power_bound {ρ Θ : ℝ} {l d : ℕ}
    (hρ : 0 ≤ ρ) (hρΘ : ρ ^ 2 ≤ Θ) (hd : d ≤ l) :
    ρ ^ 2 * ρ ^ d ≤ shiShiftedReactionScale l Θ := by
  have hΘ : 0 ≤ Θ := (sq_nonneg ρ).trans hρΘ
  have hB : 1 ≤ max 1 Θ := le_max_left _ _
  have hΘB : Θ ≤ max 1 Θ := le_max_right _ _
  have hρB : ρ ≤ max 1 Θ := by nlinarith
  have hp : ρ ^ d ≤ (max 1 Θ) ^ l :=
    (pow_le_pow_left₀ hρ hρB d).trans (pow_le_pow_right₀ hB hd)
  exact mul_le_mul hρΘ hp (pow_nonneg hρ d) hΘ

private theorem reaction_shift_le (n m l : ℕ) {ρ Θ : ℝ} (N : ℕ → ℝ)
    (hρ : 0 ≤ ρ) (hρΘ : ρ ^ 2 ≤ Θ) (hN : ∀ j, 0 ≤ N j) :
    ρ ^ 2 * (ρ ^ (m - l)) ^ 2 * reaction n m N ≤
      shiShiftedReactionScale l Θ * reaction n m (fun j => ρ ^ (j - l) * N j) := by
  let S := fun j => ρ ^ (j - l) * N j
  let Λ := shiShiftedReactionScale l Θ
  have hS (j : ℕ) : 0 ≤ S j := mul_nonneg (pow_nonneg hρ _) (hN j)
  have hterm (i : ℕ) (hi : i ≤ m) :
      ρ ^ 2 * (ρ ^ (m - l)) ^ 2 * (N m * (N i * N (m - i))) ≤
        Λ * (S m * (S i * S (m - i))) := by
    let d := m - l - ((i - l) + (m - i - l))
    have hexp : (i - l) + (m - i - l) + d = m - l := by
      dsimp [d]
      omega
    have hdl : d ≤ l := by dsimp [d]; omega
    have hp : (ρ ^ (m - l)) ^ 2 =
        ρ ^ d * ρ ^ (m - l) * ρ ^ (i - l) * ρ ^ (m - i - l) := by
      rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega
    have he : ρ ^ 2 * (ρ ^ (m - l)) ^ 2 * (N m * (N i * N (m - i))) =
        (ρ ^ 2 * ρ ^ d) * (S m * (S i * S (m - i))) := by
      rw [hp]
      dsimp [S]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (shifted_power_bound hρ hρΘ hdl)
      (mul_nonneg (hS m) (mul_nonneg (hS i) (hS (m - i))))
  have hsum : ρ ^ 2 * (ρ ^ (m - l)) ^ 2 *
      (N m * ∑ i ∈ Finset.range (m + 1), N i * N (m - i)) ≤
      Λ * (S m * ∑ i ∈ Finset.range (m + 1), S i * S (m - i)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact hterm i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hbase : ρ ^ 2 ≤ Λ := by
    simpa only [pow_zero, mul_one] using
      (shifted_power_bound hρ hρΘ (Nat.zero_le l))
  have hmetric : ρ ^ 2 * (ρ ^ (m - l)) ^ 2 * (N 0 * (N m) ^ 2) ≤
      Λ * (S 0 * (S m) ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hbase
      (mul_nonneg (hS 0) (sq_nonneg (S m)))
    dsimp [S] at h ⊢
    simp only [Nat.zero_sub, pow_zero, one_mul, mul_pow] at h ⊢
    nlinarith only [h]
  have h1 := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 2 * (n : ℝ) * (curvatureReactionWeight m : ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hmetric
    (show 0 ≤ 2 * (m + 4 : ℕ) * (n : ℝ) ^ (m + 6) by positivity)
  unfold reaction
  change _ ≤ Λ * _
  dsimp only [S] at h1 h2
  nlinarith only [h1, h2]

private theorem reaction_le (n m : ℕ) {N : ℕ → ℝ} {H : ℝ}
    (hN : ∀ j, 0 ≤ N j) (hH : 0 ≤ H) (hbound : ∀ j ≤ m, N j ≤ H) :
    reaction n m N ≤ shiEnergyReactionCoefficient n m * H ^ 3 := by
  have hsum : (∑ i ∈ Finset.range (m + 1), N i * N (m - i)) ≤
      (m + 1 : ℕ) * H ^ 2 := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (m + 1), H ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        simpa only [pow_two] using
          mul_le_mul (hbound i hi') (hbound (m - i) (Nat.sub_le m i)) (hN _) hH
      _ = _ := by simp [nsmul_eq_mul]
  have hs0 : 0 ≤ ∑ i ∈ Finset.range (m + 1), N i * N (m - i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hN _) (hN _)
  have hfirst := mul_le_mul (hbound m le_rfl) hsum hs0 hH
  have hsq : (N m) ^ 2 ≤ H ^ 2 := (sq_le_sq₀ (hN m) hH).2 (hbound m le_rfl)
  have hsecond := mul_le_mul (hbound 0 (Nat.zero_le m)) hsq (sq_nonneg (N m)) hH
  have h1 := mul_le_mul_of_nonneg_left hfirst
    (show 0 ≤ 2 * (n : ℝ) * (curvatureReactionWeight m : ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hsecond
    (show 0 ≤ 2 * (m + 4 : ℕ) * (n : ℝ) ^ (m + 6) by positivity)
  unfold reaction shiEnergyReactionCoefficient
  nlinarith only [h1, h2]

private theorem reaction_succ_le (n m : ℕ) {N : ℕ → ℝ} {H : ℝ}
    (hN : ∀ j, 0 ≤ N j) (hH : 0 ≤ H) (hbound : ∀ j ≤ m, N j ≤ H) :
    reaction n (m + 1) N ≤ shiEnergyReactionCoefficient n (m + 1) *
      (H * (N (m + 1)) ^ 2 + H ^ 2 * N (m + 1)) := by
  have hsum : (∑ i ∈ Finset.range (m + 2), N i * N (m + 1 - i)) ≤
      (m + 2 : ℕ) * (H * N (m + 1) + H ^ 2) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (m + 2), (H * N (m + 1) + H ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ m + 1 := by have := Finset.mem_range.mp hi; omega
        by_cases hi0 : i = 0
        · subst i
          simpa only [Nat.sub_zero] using
            (mul_le_mul_of_nonneg_right (hbound 0 (Nat.zero_le m)) (hN _)).trans
              (le_add_of_nonneg_right (sq_nonneg H))
        by_cases hitop : i = m + 1
        · subst i
          simp only [Nat.sub_self]
          have h := mul_le_mul_of_nonneg_left (hbound 0 (Nat.zero_le m)) (hN (m + 1))
          rw [mul_comm (N (m + 1)) H] at h
          exact h.trans (le_add_of_nonneg_right (sq_nonneg H))
        have hi'' : i ≤ m := by omega
        have hj : m + 1 - i ≤ m := by omega
        have h : N i * N (m + 1 - i) ≤ H ^ 2 := by
          simpa only [pow_two] using mul_le_mul (hbound i hi'') (hbound _ hj) (hN _) hH
        exact h.trans (le_add_of_nonneg_left (mul_nonneg hH (hN _)))
      _ = _ := by simp [nsmul_eq_mul, mul_add]
  have hfirst := mul_le_mul_of_nonneg_left hsum (hN (m + 1))
  have hsecond := mul_le_mul_of_nonneg_right (hbound 0 (Nat.zero_le m))
    (sq_nonneg (N (m + 1)))
  have hP : 0 ≤ 2 * (n : ℝ) * (curvatureReactionWeight (m + 1) : ℝ) := by positivity
  have hC : 0 ≤ 2 * (m + 1 + 4 : ℕ) * (n : ℝ) ^ (m + 1 + 6) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hfirst hP
  have h2 := mul_le_mul_of_nonneg_left hsecond hC
  have h3 := mul_nonneg hC (mul_nonneg (sq_nonneg H) (hN (m + 1)))
  unfold reaction shiEnergyReactionCoefficient
  nlinarith only [h1, h2, h3]

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

noncomputable def shiShiftedEnergy (l : ℕ) (ρ : ℝ) (D : LeviCivitaData g)
    (j : ℕ) (x : M) : ℝ :=
  (ρ ^ (j - l)) ^ 2 * (D.curvatureDerivativeNorm j x) ^ 2

private theorem energy_smooth (D : LeviCivitaData g) (j : ℕ) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => (D.curvatureDerivativeNorm j y) ^ 2) := by
  apply contMDiff_tensorNorm_sq
  induction j with
  | zero => exact isSmoothCovariantTensor_riemannEvaluation D
  | succ j ih => exact isSmoothCovariantTensor_covariantTensorDerivative D ih

private theorem laplacian_const_mul (D : LeviCivitaData g) (c : ℝ)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    D.laplacian (fun y => c * f y) x = c * D.laplacian f x := by
  have hz : D.laplacian (fun _ : M => (0 : ℝ)) x = 0 := by
    simp [LeviCivitaData.laplacian, LeviCivitaData.hessian,
      LeviCivitaData.hessianOnFields, mvfderiv_const]
  have h := laplacian_const_add_mul D c (f := fun _ => 0) contMDiff_const hf x
  simpa only [add_zero, hz, mul_zero, scalarGradientPairing,
    mvfderiv_const, zero_apply, zero_mul, Finset.sum_const_zero] using h

private theorem shifted_heat_inequality
    {T : ℝ} (F : RicciFlow n M (Icc 0 T)) {j l : ℕ} (hlj : l ≤ j)
    {ρ Θ : ℝ} (hρ : 0 ≤ ρ) (hρΘ : ρ ^ 2 ≤ Θ)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : M) :
    ρ ^ 2 * (derivWithin (fun s => shiShiftedEnergy l ρ (F.connection s) j x)
      (Icc 0 T) t - (F.connection t).laplacian (shiShiftedEnergy l ρ (F.connection t) j) x) ≤
      -2 * shiShiftedEnergy l ρ (F.connection t) (j + 1) x +
        shiShiftedReactionScale l Θ * reaction n j
          (fun i => ρ ^ (i - l) * (F.connection t).curvatureDerivativeNorm i x) := by
  have h := curvatureDerivative_heat_inequality_general_on_Icc F j ht x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  rw [hdim] at h
  have h' : derivWithin (fun s => ((F.connection s).curvatureDerivativeNorm j x) ^ 2)
      (Icc 0 T) t - (F.connection t).laplacian
        (fun y => ((F.connection t).curvatureDerivativeNorm j y) ^ 2) x ≤
      -2 * ((F.connection t).curvatureDerivativeNorm (j + 1) x) ^ 2 +
        reaction n j (fun i => (F.connection t).curvatureDerivativeNorm i x) := by
    unfold reaction
    linarith only [h]
  have hmul := mul_le_mul_of_nonneg_left h'
    (show 0 ≤ ρ ^ 2 * (ρ ^ (j - l)) ^ 2 by positivity)
  have hr := reaction_shift_le n j l
    (fun i => (F.connection t).curvatureDerivativeNorm i x) hρ hρΘ
    (fun _ => Real.sqrt_nonneg _)
  have hs : j + 1 - l = (j - l) + 1 := by omega
  unfold shiShiftedEnergy
  rw [derivWithin_const_mul_field,
    laplacian_const_mul (F.connection t) _ (energy_smooth (F.connection t) j),
    hs, pow_succ ρ (j - l)]
  nlinarith only [hmul, hr]

theorem shi_shifted_heat_bounds
    {T : ℝ} (F : RicciFlow n M (Icc 0 T)) {m l : ℕ} (hlm : l ≤ m)
    {ρ Θ H : ℝ} (hρ : 0 ≤ ρ) (hρΘ : ρ ^ 2 ≤ Θ) (hH : 0 ≤ H)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : M)
    (hbound : ∀ j ≤ m, ρ ^ (j - l) * (F.connection t).curvatureDerivativeNorm j x ≤ H) :
    let W := fun j s y => shiShiftedEnergy l ρ (F.connection s) j y
    let Λ := shiShiftedReactionScale l Θ
    (ρ ^ 2 * (derivWithin (fun s => W m s x) (Icc 0 T) t -
      (F.connection t).laplacian (W m t) x) ≤
      -2 * W (m + 1) t x + Λ * shiEnergyReactionCoefficient n m * H ^ 3) ∧
    (ρ ^ 2 * (derivWithin (fun s => W (m + 1) s x) (Icc 0 T) t -
      (F.connection t).laplacian (W (m + 1) t) x) ≤
      -2 * W (m + 2) t x +
        (Λ * shiEnergyReactionCoefficient n (m + 1) * H + 1) * W (m + 1) t x +
        (Λ * shiEnergyReactionCoefficient n (m + 1) * H ^ 2) ^ 2 / 4) := by
  let N := fun j => ρ ^ (j - l) * (F.connection t).curvatureDerivativeNorm j x
  let Λ := shiShiftedReactionScale l Θ
  have hN (j : ℕ) : 0 ≤ N j := mul_nonneg (pow_nonneg hρ _) (Real.sqrt_nonneg _)
  have hΛ : 0 ≤ Λ := shiShiftedReactionScale_nonneg l ((sq_nonneg ρ).trans hρΘ)
  have hprev := mul_le_mul_of_nonneg_left (reaction_le n m hN hH hbound) hΛ
  have htop := mul_le_mul_of_nonneg_left (reaction_succ_le n m hN hH hbound) hΛ
  have htopR : Λ * reaction n (m + 1) N ≤
      (Λ * shiEnergyReactionCoefficient n (m + 1) * H + 1) * (N (m + 1)) ^ 2 +
        (Λ * shiEnergyReactionCoefficient n (m + 1) * H ^ 2) ^ 2 / 4 := by
    nlinarith only [htop,
      sq_nonneg (N (m + 1) - Λ * shiEnergyReactionCoefficient n (m + 1) * H ^ 2 / 2)]
  have h1 := shifted_heat_inequality F hlm hρ hρΘ ht x
  have h2 := shifted_heat_inequality F (Nat.le_succ_of_le hlm) hρ hρΘ ht x
  have hE (j : ℕ) : shiShiftedEnergy l ρ (F.connection t) j x = (N j) ^ 2 := by
    simp only [shiShiftedEnergy, N, mul_pow]
  constructor
  · dsimp only
    nlinarith only [h1, hprev]
  · dsimp only
    rw [hE (m + 1)]
    nlinarith only [h2, htopR]

private theorem gradientPairing_const_mul (a b : ℝ) {f h : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h) (x : M) :
    scalarGradientPairing g (fun y => a * f y) (fun y => b * h y) x =
      a * b * scalarGradientPairing g f h x := by
  unfold scalarGradientPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mvfderiv_fun_mul mdifferentiableAt_const ((hf x).mdifferentiableAt (by simp)),
    mvfderiv_fun_mul mdifferentiableAt_const ((hh x).mdifferentiableAt (by simp)),
    mvfderiv_const, mvfderiv_const]
  simp only [smul_zero, add_zero, smul_apply, smul_eq_mul]
  ring

private theorem shifted_gradient_cross_le (D : LeviCivitaData g) {m l : ℕ}
    (hlm : l ≤ m) (ρ : ℝ) (x : M) :
    -2 * ρ ^ 2 * scalarGradientPairing g (shiShiftedEnergy l ρ D m)
      (shiShiftedEnergy l ρ D (m + 1)) x ≤
      (shiShiftedEnergy l ρ D (m + 1) x) ^ 2 +
        16 * shiShiftedEnergy l ρ D m x * shiShiftedEnergy l ρ D (m + 2) x := by
  have h := curvatureDerivativeEnergy_gradient_cross_le D m x
  have hmul := mul_le_mul_of_nonneg_left h
    (show 0 ≤ ρ ^ 2 * (ρ ^ (m - l)) ^ 2 * (ρ ^ (m + 1 - l)) ^ 2 by positivity)
  change -2 * ρ ^ 2 * scalarGradientPairing g
    (fun y => (ρ ^ (m - l)) ^ 2 * (D.curvatureDerivativeNorm m y) ^ 2)
    (fun y => (ρ ^ (m + 1 - l)) ^ 2 * (D.curvatureDerivativeNorm (m + 1) y) ^ 2) x ≤ _
  rw [gradientPairing_const_mul _ _ (energy_smooth D m) (energy_smooth D (m + 1)) x]
  have hs1 : m + 1 - l = m - l + 1 := by omega
  have hs2 : m + 2 - l = m - l + 2 := by omega
  simp only [shiShiftedEnergy, hs1, hs2, pow_add, pow_one] at hmul ⊢
  nlinarith only [hmul]

private theorem product_heat_bound {B u v w β γ C₀ X : ℝ}
    (hB : 0 ≤ B) (hu : 0 ≤ u) (huB : u ≤ B) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hX : X ≤ (8 * B + 1 + u) * (-2 * w + β * v + γ) +
      v * (-2 * v + C₀) + v ^ 2 + 16 * u * w) :
    X ≤ -((8 * B + 1 + u) * v) ^ 2 / (2 * (9 * B + 1) ^ 2) +
      (C₀ + β * (9 * B + 1)) ^ 2 / 2 + γ * (9 * B + 1) := by
  have hA0 : 0 ≤ 8 * B + 1 + u := by linarith
  have hAD : 8 * B + 1 + u ≤ 9 * B + 1 := by linarith
  have hD : 0 < 9 * B + 1 := by linarith
  have hwc : (-2 * (8 * B + 1) + 14 * u) * w ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hw
  have hbv := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAD hβ) hv
  have hga := mul_le_mul_of_nonneg_left hAD hγ
  have hquad : X ≤ -v ^ 2 + (C₀ + β * (9 * B + 1)) * v + γ * (9 * B + 1) := by
    nlinarith only [hX, hwc, hbv, hga]
  have hhalf : X ≤ -v ^ 2 / 2 +
      (C₀ + β * (9 * B + 1)) ^ 2 / 2 + γ * (9 * B + 1) := by
    nlinarith only [hquad, sq_nonneg (v - (C₀ + β * (9 * B + 1)))]
  have hsq : ((8 * B + 1 + u) * v) ^ 2 ≤ (9 * B + 1) ^ 2 * v ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ hA0 hD.le).2 hAD) (sq_nonneg v)
  have hdiv : ((8 * B + 1 + u) * v) ^ 2 / (2 * (9 * B + 1) ^ 2) ≤ v ^ 2 / 2 := by
    apply (div_le_iff₀ (show 0 < 2 * (9 * B + 1) ^ 2 by positivity)).2
    nlinarith only [hsq]
  have hneg : -v ^ 2 / 2 ≤ -((8 * B + 1 + u) * v) ^ 2 / (2 * (9 * B + 1) ^ 2) := by
    simpa only [neg_div] using neg_le_neg hdiv
  exact hhalf.trans (add_le_add (add_le_add hneg le_rfl) le_rfl)

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem shi_shifted_bernstein_heat_inequality
    {T : ℝ} (F : RicciFlow n M (Icc 0 T)) {m l : ℕ} (hlm : l ≤ m)
    {ρ Θ H : ℝ} (hρ : 0 ≤ ρ) (hρΘ : ρ ^ 2 ≤ Θ) (hH : 0 ≤ H)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : M)
    (hbound : ∀ j ≤ m, ρ ^ (j - l) * (F.connection t).curvatureDerivativeNorm j x ≤ H) :
    let W := fun j s y => shiShiftedEnergy l ρ (F.connection s) j y
    let Q := fun s y => (8 * H ^ 2 + 1 + W m s y) * W (m + 1) s y
    let D := 9 * H ^ 2 + 1
    let Λ := shiShiftedReactionScale l Θ
    let C₀ := Λ * shiEnergyReactionCoefficient n m * H ^ 3
    let β := Λ * shiEnergyReactionCoefficient n (m + 1) * H + 1
    let γ := (Λ * shiEnergyReactionCoefficient n (m + 1) * H ^ 2) ^ 2 / 4
    ρ ^ 2 * (derivWithin (fun s => Q s x) (Icc 0 T) t -
      (F.connection t).laplacian (Q t) x) ≤
      -(Q t x) ^ 2 / (2 * D ^ 2) + (C₀ + β * D) ^ 2 / 2 + γ * D := by
  let W := fun j s y => shiShiftedEnergy l ρ (F.connection s) j y
  let A := 8 * H ^ 2 + 1
  let Q := fun s y => (A + W m s y) * W (m + 1) s y
  let Λ := shiShiftedReactionScale l Θ
  let C₀ := Λ * shiEnergyReactionCoefficient n m * H ^ 3
  let β := Λ * shiEnergyReactionCoefficient n (m + 1) * H + 1
  let γ := (Λ * shiEnergyReactionCoefficient n (m + 1) * H ^ 2) ^ 2 / 4
  have hΛ : 0 ≤ Λ := shiShiftedReactionScale_nonneg l ((sq_nonneg ρ).trans hρΘ)
  have hspace (j : ℕ) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (W j t) :=
    contMDiff_const.mul (energy_smooth (F.connection t) j)
  have htime (j : ℕ) : DifferentiableWithinAt ℝ (fun s => W j s x) (Icc 0 T) t := by
    have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun s : ℝ => (s, x)) := contMDiff_id.prodMk contMDiff_const
    have hE : ContDiffOn ℝ ∞
        (fun s => ((F.connection s).curvatureDerivativeNorm j x) ^ 2) (Icc 0 T) :=
      (contMDiffOn_flow_curvatureDerivativeEnergy F j).comp
        hslice.contMDiffOn (fun s hs => ⟨hs, mem_univ x⟩) |>.contDiffOn
    exact (hE.differentiableOn (by simp) t ⟨ht.1.le, ht.2⟩).const_mul ((ρ ^ (j - l)) ^ 2)
  have hdt : derivWithin (fun s => Q s x) (Icc 0 T) t =
      derivWithin (fun s => W m s x) (Icc 0 T) t * W (m + 1) t x +
        (A + W m t x) * derivWithin (fun s => W (m + 1) s x) (Icc 0 T) t := by
    change derivWithin (fun s => (A + W m s x) * W (m + 1) s x) (Icc 0 T) t = _
    rw [derivWithin_fun_mul ((htime m).const_add A) (htime (m + 1)),
      derivWithin_const_add_fun]
  have hlap : (F.connection t).laplacian (Q t) x =
      (A + W m t x) * (F.connection t).laplacian (W (m + 1) t) x +
        W (m + 1) t x * (F.connection t).laplacian (W m t) x +
          2 * scalarGradientPairing (F.metric t) (W m t) (W (m + 1) t) x :=
    laplacian_const_add_mul (F.connection t) A (hspace m) (hspace (m + 1)) x
  have hprod : ρ ^ 2 * (derivWithin (fun s => Q s x) (Icc 0 T) t -
      (F.connection t).laplacian (Q t) x) =
      (A + W m t x) * (ρ ^ 2 * (derivWithin (fun s => W (m + 1) s x) (Icc 0 T) t -
        (F.connection t).laplacian (W (m + 1) t) x)) +
      W (m + 1) t x * (ρ ^ 2 * (derivWithin (fun s => W m s x) (Icc 0 T) t -
        (F.connection t).laplacian (W m t) x)) -
      2 * ρ ^ 2 * scalarGradientPairing (F.metric t) (W m t) (W (m + 1) t) x := by
    rw [hdt, hlap]
    ring
  have hW (j : ℕ) : 0 ≤ W j t x := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hWm : W m t x ≤ H ^ 2 := by
    change (ρ ^ (m - l)) ^ 2 * ((F.connection t).curvatureDerivativeNorm m x) ^ 2 ≤ H ^ 2
    rw [← mul_pow]
    exact (sq_le_sq₀
      (mul_nonneg (pow_nonneg hρ _) (Real.sqrt_nonneg _)) hH).2 (hbound m le_rfl)
  have hA : 0 ≤ A + W m t x := by
    dsimp only [A]
    have := hW m
    positivity
  have hβ : 0 ≤ β := by
    have hc := shiEnergyReactionCoefficient_nonneg n (m + 1)
    dsimp only [β]
    positivity
  have hγ : 0 ≤ γ := by dsimp only [γ]; positivity
  obtain ⟨hprev, hnext⟩ := shi_shifted_heat_bounds F hlm hρ hρΘ hH ht x hbound
  have hnext' := mul_le_mul_of_nonneg_left hnext hA
  have hprev' := mul_le_mul_of_nonneg_left hprev (hW (m + 1))
  have hcross := shifted_gradient_cross_le (F.connection t) hlm ρ x
  have hineq : ρ ^ 2 * (derivWithin (fun s => Q s x) (Icc 0 T) t -
      (F.connection t).laplacian (Q t) x) ≤
      (A + W m t x) * (-2 * W (m + 2) t x + β * W (m + 1) t x + γ) +
        W (m + 1) t x * (-2 * W (m + 1) t x + C₀) +
        (W (m + 1) t x) ^ 2 + 16 * W m t x * W (m + 2) t x := by
    rw [hprod]
    dsimp only [W, C₀, β, γ] at hnext' hprev' ⊢
    nlinarith only [hnext', hprev', hcross]
  exact product_heat_bound (sq_nonneg H) (hW m) hWm (hW (m + 1))
    (hW (m + 2)) hβ hγ hineq

end PoincareConjecture.M04

