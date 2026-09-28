import PoincareConjecture.Proofs.M04.ShiBernsteinEnergy
import PoincareConjecture.Proofs.M04.ShiHeatBridgeGeneral

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

noncomputable def shiEnergyReactionCoefficient (n m : ℕ) : ℝ :=
  2 * (n : ℝ) * (curvatureReactionWeight m : ℝ) * (m + 1 : ℕ) +
    2 * (m + 4 : ℕ) * (n : ℝ) ^ (m + 6)

private noncomputable def reactionPolynomial (n m : ℕ) (N : ℕ → ℝ) : ℝ :=
  2 * (n : ℝ) * (curvatureReactionWeight m : ℝ) * N m *
    (∑ i ∈ Finset.range (m + 1), N i * N (m - i)) +
    2 * (m + 4 : ℕ) * (n : ℝ) ^ (m + 6) * N 0 * (N m) ^ 2

theorem shiEnergyReactionCoefficient_nonneg (n m : ℕ) :
    0 ≤ shiEnergyReactionCoefficient n m := by
  unfold shiEnergyReactionCoefficient
  positivity

private theorem reactionPolynomial_scale (n m : ℕ) (ρ : ℝ) (N : ℕ → ℝ) :
    reactionPolynomial n m (fun j => ρ ^ j * N j) =
      (ρ ^ m) ^ 2 * reactionPolynomial n m N := by
  have hs : (∑ i ∈ Finset.range (m + 1),
      (ρ ^ i * N i) * (ρ ^ (m - i) * N (m - i))) =
      ρ ^ m * (∑ i ∈ Finset.range (m + 1), N i * N (m - i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have him : i ≤ m := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    calc
      _ = (ρ ^ i * ρ ^ (m - i)) * (N i * N (m - i)) := by ring
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le him]
  unfold reactionPolynomial
  rw [hs]
  simp only [pow_zero, one_mul]
  ring

private theorem reactionPolynomial_le_of_bound
    (n m : ℕ) {N : ℕ → ℝ} {H : ℝ} (hN : ∀ j, 0 ≤ N j)
    (hH : 0 ≤ H) (hbound : ∀ j ≤ m, N j ≤ H) :
    reactionPolynomial n m N ≤ shiEnergyReactionCoefficient n m * H ^ 3 := by
  have hsum : (∑ i ∈ Finset.range (m + 1), N i * N (m - i)) ≤
      (m + 1 : ℕ) * H ^ 2 := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (m + 1), H ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have h := mul_le_mul (hbound i hi') (hbound (m - i) (Nat.sub_le m i))
          (hN (m - i)) hH
        simpa only [pow_two] using h
      _ = _ := by simp [nsmul_eq_mul]
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range (m + 1), N i * N (m - i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hN i) (hN (m - i))
  have hfirst := mul_le_mul (hbound m le_rfl) hsum hsum0 hH
  have hsq : (N m) ^ 2 ≤ H ^ 2 := by nlinarith [hbound m le_rfl, hN m]
  have hsecond := mul_le_mul (hbound 0 (Nat.zero_le m)) hsq (sq_nonneg (N m)) hH
  have hP : 0 ≤ 2 * (n : ℝ) * (curvatureReactionWeight m : ℝ) := by positivity
  have hC : 0 ≤ 2 * (m + 4 : ℕ) * (n : ℝ) ^ (m + 6) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hfirst hP
  have h2 := mul_le_mul_of_nonneg_left hsecond hC
  unfold reactionPolynomial shiEnergyReactionCoefficient
  nlinarith only [h1, h2]

private theorem reactionPolynomial_succ_le_of_bound
    (n m : ℕ) {N : ℕ → ℝ} {H : ℝ} (hN : ∀ j, 0 ≤ N j)
    (hH : 0 ≤ H) (hbound : ∀ j ≤ m, N j ≤ H) :
    reactionPolynomial n (m + 1) N ≤
      shiEnergyReactionCoefficient n (m + 1) *
        (H * (N (m + 1)) ^ 2 + H ^ 2 * N (m + 1)) := by
  have hsum : (∑ i ∈ Finset.range (m + 1 + 1), N i * N (m + 1 - i)) ≤
      (m + 1 + 1 : ℕ) * (H * N (m + 1) + H ^ 2) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (m + 1 + 1), (H * N (m + 1) + H ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ m + 1 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        by_cases hi0 : i = 0
        · subst i
          simp only [Nat.sub_zero]
          exact (mul_le_mul_of_nonneg_right (hbound 0 (Nat.zero_le m)) (hN _)).trans
            (le_add_of_nonneg_right (sq_nonneg H))
        by_cases hitop : i = m + 1
        · subst i
          simp only [Nat.sub_self]
          have h := mul_le_mul_of_nonneg_left (hbound 0 (Nat.zero_le m)) (hN (m + 1))
          rw [mul_comm (N (m + 1)) H] at h
          exact h.trans (le_add_of_nonneg_right (sq_nonneg H))
        have hi'' : i ≤ m := by omega
        have hother : m + 1 - i ≤ m := by omega
        have h := mul_le_mul (hbound i hi'') (hbound _ hother) (hN _) hH
        have hs : N i * N (m + 1 - i) ≤ H ^ 2 := by simpa only [pow_two] using h
        exact hs.trans (le_add_of_nonneg_left (mul_nonneg hH (hN _)))
      _ = _ := by simp [nsmul_eq_mul, mul_add]
  have hfirst := mul_le_mul_of_nonneg_left hsum (hN (m + 1))
  have hsecond := mul_le_mul_of_nonneg_right (hbound 0 (Nat.zero_le m))
    (sq_nonneg (N (m + 1)))
  have hP : 0 ≤ 2 * (n : ℝ) * (curvatureReactionWeight (m + 1) : ℝ) := by positivity
  have hC : 0 ≤ 2 * (m + 1 + 4 : ℕ) * (n : ℝ) ^ (m + 1 + 6) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hfirst hP
  have h2 := mul_le_mul_of_nonneg_left hsecond hC
  have hextra := mul_nonneg hC (mul_nonneg (sq_nonneg H) (hN (m + 1)))
  unfold reactionPolynomial shiEnergyReactionCoefficient
  nlinarith only [h1, h2, hextra]

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

noncomputable def shiScaledEnergy (ρ : ℝ) (D : LeviCivitaData g) (m : ℕ) (x : M) : ℝ :=
  (ρ ^ m) ^ 2 * (D.curvatureDerivativeNorm m x) ^ 2

private theorem energy_smooth (D : LeviCivitaData g) (m : ℕ) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => (D.curvatureDerivativeNorm m y) ^ 2) := by
  apply contMDiff_tensorNorm_sq
  induction m with
  | zero => exact isSmoothCovariantTensor_riemannEvaluation D
  | succ m ih => exact isSmoothCovariantTensor_covariantTensorDerivative D ih

private theorem laplacian_const_mul (D : LeviCivitaData g) (c : ℝ)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    D.laplacian (fun y => c * f y) x = c * D.laplacian f x := by
  have hz : D.laplacian (fun _ : M => (0 : ℝ)) x = 0 := by
    simp [LeviCivitaData.laplacian, LeviCivitaData.hessian,
      LeviCivitaData.hessianOnFields, mvfderiv_const]
  have h := laplacian_const_add_mul D c (f := fun _ => 0) contMDiff_const hf x
  simpa only [add_zero, hz, mul_zero, scalarGradientPairing,
    mvfderiv_const, zero_apply, zero_mul, Finset.sum_const_zero] using h

private theorem scaled_heat_inequality
    {T : ℝ} (F : RicciFlow n M (Icc 0 T)) (m : ℕ) (ρ : ℝ)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : M) :
    ρ ^ 2 * (derivWithin (fun s => shiScaledEnergy ρ (F.connection s) m x) (Icc 0 T) t -
      (F.connection t).laplacian (shiScaledEnergy ρ (F.connection t) m) x) ≤
      -2 * shiScaledEnergy ρ (F.connection t) (m + 1) x +
        ρ ^ 2 * reactionPolynomial n m
          (fun j => ρ ^ j * (F.connection t).curvatureDerivativeNorm j x) := by
  have h := curvatureDerivative_heat_inequality_general_on_Icc F m ht x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  rw [hdim] at h
  have h' : derivWithin (fun s => ((F.connection s).curvatureDerivativeNorm m x) ^ 2)
      (Icc 0 T) t - (F.connection t).laplacian
        (fun y => ((F.connection t).curvatureDerivativeNorm m y) ^ 2) x ≤
      -2 * ((F.connection t).curvatureDerivativeNorm (m + 1) x) ^ 2 +
        reactionPolynomial n m (fun j => (F.connection t).curvatureDerivativeNorm j x) := by
    unfold reactionPolynomial
    linarith only [h]
  have hmul := mul_le_mul_of_nonneg_left h' (show 0 ≤ ρ ^ 2 * (ρ ^ m) ^ 2 by positivity)
  change ρ ^ 2 * (derivWithin
      (fun s => (ρ ^ m) ^ 2 * ((F.connection s).curvatureDerivativeNorm m x) ^ 2)
      (Icc 0 T) t - (F.connection t).laplacian
        (fun y => (ρ ^ m) ^ 2 * ((F.connection t).curvatureDerivativeNorm m y) ^ 2) x) ≤
    -2 * ((ρ ^ (m + 1)) ^ 2 * ((F.connection t).curvatureDerivativeNorm (m + 1) x) ^ 2) + _
  rw [reactionPolynomial_scale, derivWithin_const_mul_field,
    laplacian_const_mul (F.connection t) _ (energy_smooth (F.connection t) m), pow_succ ρ m]
  nlinarith only [hmul]

theorem shi_scaled_heat_bounds
    {T : ℝ} (F : RicciFlow n M (Icc 0 T)) (m : ℕ) {ρ Θ H : ℝ}
    (hρ : 0 ≤ ρ) (hρΘ : ρ ^ 2 ≤ Θ) (hH : 0 ≤ H)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : M)
    (hbound : ∀ j ≤ m, ρ ^ j * (F.connection t).curvatureDerivativeNorm j x ≤ H) :
    let W := fun j s y => shiScaledEnergy ρ (F.connection s) j y
    (ρ ^ 2 * (derivWithin (fun s => W m s x) (Icc 0 T) t -
      (F.connection t).laplacian (W m t) x) ≤
      -2 * W (m + 1) t x + Θ * shiEnergyReactionCoefficient n m * H ^ 3) ∧
    (ρ ^ 2 * (derivWithin (fun s => W (m + 1) s x) (Icc 0 T) t -
      (F.connection t).laplacian (W (m + 1) t) x) ≤
      -2 * W (m + 2) t x +
        (Θ * shiEnergyReactionCoefficient n (m + 1) * H + 1) * W (m + 1) t x +
        (Θ * shiEnergyReactionCoefficient n (m + 1) * H ^ 2) ^ 2 / 4) := by
  let N := fun j => ρ ^ j * (F.connection t).curvatureDerivativeNorm j x
  have hN (j : ℕ) : 0 ≤ N j :=
    mul_nonneg (pow_nonneg hρ j) (Real.sqrt_nonneg _)
  have hΘ : 0 ≤ Θ := (sq_nonneg ρ).trans hρΘ
  have hprev := reactionPolynomial_le_of_bound n m hN hH hbound
  have htop := reactionPolynomial_succ_le_of_bound n m hN hH hbound
  have hprevR : ρ ^ 2 * reactionPolynomial n m N ≤
      Θ * shiEnergyReactionCoefficient n m * H ^ 3 := by
    calc
      _ ≤ ρ ^ 2 * (shiEnergyReactionCoefficient n m * H ^ 3) :=
        mul_le_mul_of_nonneg_left hprev (sq_nonneg ρ)
      _ ≤ Θ * (shiEnergyReactionCoefficient n m * H ^ 3) :=
        mul_le_mul_of_nonneg_right hρΘ
          (mul_nonneg (shiEnergyReactionCoefficient_nonneg n m) (pow_nonneg hH 3))
      _ = _ := by ring
  have htopR : ρ ^ 2 * reactionPolynomial n (m + 1) N ≤
      (Θ * shiEnergyReactionCoefficient n (m + 1) * H + 1) * (N (m + 1)) ^ 2 +
        (Θ * shiEnergyReactionCoefficient n (m + 1) * H ^ 2) ^ 2 / 4 := by
    have hNm := hN (m + 1)
    have hR : ρ ^ 2 * reactionPolynomial n (m + 1) N ≤
        Θ * (shiEnergyReactionCoefficient n (m + 1) *
          (H * (N (m + 1)) ^ 2 + H ^ 2 * N (m + 1))) := by
      exact (mul_le_mul_of_nonneg_left htop (sq_nonneg ρ)).trans
        (mul_le_mul_of_nonneg_right hρΘ (mul_nonneg
          (shiEnergyReactionCoefficient_nonneg n (m + 1)) (by positivity)))
    nlinarith only [hR,
      sq_nonneg (N (m + 1) - Θ * shiEnergyReactionCoefficient n (m + 1) * H ^ 2 / 2)]
  have h1 := scaled_heat_inequality F m ρ ht x
  have h2 := scaled_heat_inequality F (m + 1) ρ ht x
  have hE (j : ℕ) : shiScaledEnergy ρ (F.connection t) j x = (N j) ^ 2 := by
    simp only [shiScaledEnergy, N, mul_pow]
  constructor
  · dsimp only
    nlinarith only [h1, hprevR]
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

private theorem scaled_gradient_cross_le (D : LeviCivitaData g) (m : ℕ) (ρ : ℝ) (x : M) :
    -2 * ρ ^ 2 * scalarGradientPairing g (shiScaledEnergy ρ D m)
      (shiScaledEnergy ρ D (m + 1)) x ≤
      (shiScaledEnergy ρ D (m + 1) x) ^ 2 +
        16 * shiScaledEnergy ρ D m x * shiScaledEnergy ρ D (m + 2) x := by
  have h := curvatureDerivativeEnergy_gradient_cross_le D m x
  have hmul := mul_le_mul_of_nonneg_left h
    (show 0 ≤ ρ ^ 2 * (ρ ^ m) ^ 2 * (ρ ^ (m + 1)) ^ 2 by positivity)
  change -2 * ρ ^ 2 * scalarGradientPairing g
    (fun y => (ρ ^ m) ^ 2 * (D.curvatureDerivativeNorm m y) ^ 2)
    (fun y => (ρ ^ (m + 1)) ^ 2 * (D.curvatureDerivativeNorm (m + 1) y) ^ 2) x ≤ _
  rw [gradientPairing_const_mul _ _ (energy_smooth D m) (energy_smooth D (m + 1)) x]
  simp only [shiScaledEnergy, pow_add, pow_one] at hmul ⊢
  nlinarith only [hmul]

private theorem bernstein_product_bound {B u v w β γ C₀ X : ℝ}
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
theorem shi_bernstein_heat_inequality
    {T : ℝ} (F : RicciFlow n M (Icc 0 T)) (m : ℕ) {ρ Θ H : ℝ}
    (hρ : 0 ≤ ρ) (hρΘ : ρ ^ 2 ≤ Θ) (hH : 0 ≤ H)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : M)
    (hbound : ∀ j ≤ m, ρ ^ j * (F.connection t).curvatureDerivativeNorm j x ≤ H) :
    let W := fun j s y => shiScaledEnergy ρ (F.connection s) j y
    let Q := fun s y => (8 * H ^ 2 + 1 + W m s y) * W (m + 1) s y
    let D := 9 * H ^ 2 + 1
    let C₀ := Θ * shiEnergyReactionCoefficient n m * H ^ 3
    let β := Θ * shiEnergyReactionCoefficient n (m + 1) * H + 1
    let γ := (Θ * shiEnergyReactionCoefficient n (m + 1) * H ^ 2) ^ 2 / 4
    ρ ^ 2 * (derivWithin (fun s => Q s x) (Icc 0 T) t -
      (F.connection t).laplacian (Q t) x) ≤
      -(Q t x) ^ 2 / (2 * D ^ 2) + (C₀ + β * D) ^ 2 / 2 + γ * D := by
  let W := fun j s y => shiScaledEnergy ρ (F.connection s) j y
  let A := 8 * H ^ 2 + 1
  let Q := fun s y => (A + W m s y) * W (m + 1) s y
  let C₀ := Θ * shiEnergyReactionCoefficient n m * H ^ 3
  let β := Θ * shiEnergyReactionCoefficient n (m + 1) * H + 1
  let γ := (Θ * shiEnergyReactionCoefficient n (m + 1) * H ^ 2) ^ 2 / 4
  have hΘ : 0 ≤ Θ := (sq_nonneg ρ).trans hρΘ
  have hspace (j : ℕ) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (W j t) :=
    contMDiff_const.mul (energy_smooth (F.connection t) j)
  have htime (j : ℕ) : DifferentiableWithinAt ℝ (fun s => W j s x) (Icc 0 T) t := by
    have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun s : ℝ => (s, x)) := contMDiff_id.prodMk contMDiff_const
    have hE : ContDiffOn ℝ ∞
        (fun s => ((F.connection s).curvatureDerivativeNorm j x) ^ 2) (Icc 0 T) :=
      (contMDiffOn_flow_curvatureDerivativeEnergy F j).comp
        hslice.contMDiffOn (fun s hs => ⟨hs, mem_univ x⟩) |>.contDiffOn
    exact (hE.differentiableOn (by simp) t ⟨ht.1.le, ht.2⟩).const_mul ((ρ ^ j) ^ 2)
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
    change (ρ ^ m) ^ 2 * ((F.connection t).curvatureDerivativeNorm m x) ^ 2 ≤ H ^ 2
    rw [← mul_pow]
    exact (sq_le_sq₀
      (mul_nonneg (pow_nonneg hρ m) (Real.sqrt_nonneg _)) hH).2 (hbound m le_rfl)
  have hA : 0 ≤ A + W m t x := by
    dsimp only [A]
    have := hW m
    positivity
  have hβ : 0 ≤ β := by
    have hc := shiEnergyReactionCoefficient_nonneg n (m + 1)
    dsimp only [β]
    positivity
  have hγ : 0 ≤ γ := by dsimp only [γ]; positivity
  obtain ⟨hprev, hnext⟩ := shi_scaled_heat_bounds F m hρ hρΘ hH ht x hbound
  have hnext' := mul_le_mul_of_nonneg_left hnext hA
  have hprev' := mul_le_mul_of_nonneg_left hprev (hW (m + 1))
  have hcross := scaled_gradient_cross_le (F.connection t) m ρ x
  have hineq : ρ ^ 2 * (derivWithin (fun s => Q s x) (Icc 0 T) t -
      (F.connection t).laplacian (Q t) x) ≤
      (A + W m t x) * (-2 * W (m + 2) t x + β * W (m + 1) t x + γ) +
        W (m + 1) t x * (-2 * W (m + 1) t x + C₀) +
        (W (m + 1) t x) ^ 2 + 16 * W m t x * W (m + 2) t x := by
    rw [hprod]
    dsimp only [W, C₀, β, γ] at hnext' hprev' ⊢
    nlinarith only [hnext', hprev', hcross]
  exact bernstein_product_bound (sq_nonneg H) (hW m) hWm (hW (m + 1))
    (hW (m + 2)) hβ hγ hineq

end PoincareConjecture.M04
