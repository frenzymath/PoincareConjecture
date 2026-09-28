import PoincareConjecture.Proofs.M35.RadialGauge.SourceBounds

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {A : Type*}

local notation "V" => EuclideanSpace ℝ (Fin n)

private theorem positive_order_id_bound {j : ℕ} (hj : 1 ≤ j) (x : V) :
    ‖iteratedFDeriv ℝ j (fun y : V => y) x‖ ≤ 1 := by
  cases j with
  | zero => omega
  | succ j =>
      rw [← norm_iteratedFDeriv_fderiv]
      have hid : fderiv ℝ (fun y : V => y) = fun _ => ContinuousLinearMap.id ℝ V :=
        funext (fun y => (hasFDerivAt_id y).fderiv)
      rw [hid]
      cases j with
      | zero =>
          rw [norm_iteratedFDeriv_zero]
          exact ContinuousLinearMap.norm_id_le
      | succ j => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, zero_le_one]

theorem forcing_composition_bounded_at_order
    {G : A → V → ℝ → ℝ} {u : A → V → ℝ} {eta : ℝ} (k : ℕ)
    (hG : ∀ a, ContDiff ℝ ∞ (fun p : V × ℝ => G a p.1 p.2))
    (hu : ∀ a, ContDiff ℝ ∞ (u a)) (huvalue : ∀ a x, |u a x| ≤ eta)
    (hub : ∀ j : ℕ, j ≤ k → ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ j (u a) x‖ ≤ C)
    (hGb : ∀ j : ℕ, ∃ C : ℝ, ∀ a x z, |z| ≤ eta →
      ‖iteratedFDeriv ℝ j (fun p : V × ℝ => G a p.1 p.2) (x, z)‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a x,
      ‖iteratedFDeriv ℝ k (fun y => G a y (u a y)) x‖ ≤ C := by
  classical
  have hub' : ∀ j : ℕ, ∃ C : ℝ, j ≤ k → ∀ a x,
      ‖iteratedFDeriv ℝ j (u a) x‖ ≤ C := by
    intro j
    by_cases hj : j ≤ k
    · obtain ⟨C, hC⟩ := hub j hj
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => (hj h).elim⟩
  choose U hU using hub'
  choose B hB using hGb
  let C := ∑ j ∈ Finset.range (k + 1), |B j|
  let D := 1 + ∑ j ∈ Finset.range (k + 1), |U j|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hD : 1 ≤ D := by
    dsimp [D]
    linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (k + 1)) => abs_nonneg (U j))]
  have hBle {j : ℕ} (hj : j ≤ k) : B j ≤ C :=
    (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (B i))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
  have hUle {j : ℕ} (hj : j ≤ k) : U j ≤ D := by
    have h := (le_abs_self (U j)).trans
      (Finset.single_le_sum (fun i _ => abs_nonneg (U i))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
    dsimp [D]
    linarith
  refine ⟨(k.factorial : ℝ) * C * D ^ k, by positivity, fun a x => ?_⟩
  have h := norm_iteratedFDeriv_comp_le (hG a) (contDiff_id.prodMk (hu a))
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl k) x
    (C := C) (D := D)
    (fun j hj => (hB j a x (u a x) (huvalue a x)).trans (hBle hj))
    (fun j hj hjk => ?_)
  · simpa only [Function.comp_def, id_eq] using h
  · rw [iteratedFDeriv_prodMk contDiffAt_id (hu a).contDiffAt
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j), ContinuousMultilinearMap.opNorm_prod]
    exact (max_le ((positive_order_id_bound hj x).trans hD)
      ((hU j hjk a x).trans (hUle hjk))).trans (le_self_pow₀ hD (by omega))

theorem gaugeSource_highest_jet_bound
    {b : A → V → V} {G : A → V → ℝ → ℝ} {u : A → V → ℝ}
    {eta B : ℝ} (heta : 0 ≤ eta) (k : ℕ) (hk : 1 ≤ k)
    (hb : ∀ a, ContDiff ℝ ∞ (b a))
    (hG : ∀ a, ContDiff ℝ ∞ (fun p : V × ℝ => G a p.1 p.2))
    (hu : ∀ a, ContDiff ℝ ∞ (u a)) (huvalue : ∀ a x, |u a x| ≤ eta)
    (hp : ∀ a x, ‖fderiv ℝ (u a) x‖ ≤ eta) (hbb0 : ∀ a x, ‖b a x‖ ≤ B)
    (hbb : ∀ j : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ j (b a) x‖ ≤ C)
    (hub : ∀ j : ℕ, j ≤ k → ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ j (u a) x‖ ≤ C)
    (hGb : ∀ j : ℕ, ∃ C : ℝ, ∀ a x z, |z| ≤ eta →
      ‖iteratedFDeriv ℝ j (fun p : V × ℝ => G a p.1 p.2) (x, z)‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a x,
      ‖iteratedFDeriv ℝ k (gaugeSource (b a) (G a) (u a)) x‖ ≤
        (B + 2 * (n : ℝ) * eta) * ‖iteratedFDeriv ℝ (k + 1) (u a) x‖ + C := by
  classical
  have hub' : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (j ≤ k → ∀ a x,
      ‖iteratedFDeriv ℝ j (u a) x‖ ≤ C) := by
    intro j
    by_cases hj : j ≤ k
    · obtain ⟨C, hC⟩ := hub j hj
      exact ⟨max C 0, le_max_right _ _, fun _ a x => (hC a x).trans (le_max_left _ _)⟩
    · exact ⟨0, le_rfl, fun h => (hj h).elim⟩
  have hbb' : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x,
      ‖iteratedFDeriv ℝ j (b a) x‖ ≤ C := by
    intro j
    obtain ⟨C, hC⟩ := hbb j
    exact ⟨max C 0, le_max_right _ _, fun a x => (hC a x).trans (le_max_left _ _)⟩
  choose U hU0 hU using hub'
  choose D hD0 hD using hbb'
  obtain ⟨C0, hC0, hforcing⟩ := forcing_composition_bounded_at_order k hG hu huvalue hub hGb
  let Cd := ∑ i ∈ Finset.range k, (k.choose i : ℝ) * U (i + 1) * D (k - i)
  let Cq := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * U (i + 1) * U (k - i + 1)
  have hCd : 0 ≤ Cd := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hU0 _)) (hD0 _))
  have hCq : 0 ≤ Cq := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hU0 _)) (hU0 _))
  have hdu (a : A) := (contDiff_infty_iff_fderiv.mp (hu a)).2
  have hdrift (a : A) (x : V) :
      ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ (u a) y (b a y)) x‖ ≤
        B * ‖iteratedFDeriv ℝ (k + 1) (u a) x‖ + Cd := by
    have h := norm_iteratedFDeriv_clm_apply (hdu a) (hb a) x
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
    rw [Finset.sum_range_succ] at h
    have hsum : (∑ i ∈ Finset.range k, (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fderiv ℝ (u a)) x‖ * ‖iteratedFDeriv ℝ (k - i) (b a) x‖) ≤ Cd := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_iteratedFDeriv_fderiv]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hU (i + 1) (by have := Finset.mem_range.mp hi; omega) a x)
          (Nat.cast_nonneg _)) (hD (k - i) a x) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (hU0 _))
    have htop := mul_le_mul_of_nonneg_left (hbb0 a x)
      (norm_nonneg (iteratedFDeriv ℝ (k + 1) (u a) x))
    simp only [Nat.choose_self, Nat.cast_one, one_mul, norm_iteratedFDeriv_fderiv] at h
    have hzero : ‖iteratedFDeriv ℝ (k - k) (b a) x‖ = ‖b a x‖ := by
      rw [Nat.sub_self, norm_iteratedFDeriv_zero]
    rw [hzero] at h
    simp only [norm_iteratedFDeriv_fderiv] at hsum
    nlinarith only [h, hsum, htop]
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hcomponent (i : Fin n) (a : A) (j : ℕ) (x : V) :
      ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ (u a) y (e i)) x‖ ≤
        ‖iteratedFDeriv ℝ (j + 1) (u a) x‖ := by
    have he : ‖e i‖ = 1 := (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i
    simpa only [he, one_mul, norm_iteratedFDeriv_fderiv] using
      (norm_iteratedFDeriv_clm_apply_const (hdu a).contDiffAt
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl j) (c := e i) (x := x))
  have hcomponent0 (i : Fin n) (a : A) (x : V) : |fderiv ℝ (u a) x (e i)| ≤ eta := by
    have h := (fderiv ℝ (u a) x).le_opNorm (e i)
    have he : ‖e i‖ = 1 := (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i
    rw [Real.norm_eq_abs, he, mul_one] at h
    exact h.trans (hp a x)
  have hsquare (i : Fin n) (a : A) (x : V) :
      ‖iteratedFDeriv ℝ k (fun y => (fderiv ℝ (u a) y (e i)) ^ 2) x‖ ≤
        2 * eta * ‖iteratedFDeriv ℝ (k + 1) (u a) x‖ + Cq := by
    let p := fun y => fderiv ℝ (u a) y (e i)
    have hps : ContDiff ℝ ∞ p := (hdu a).clm_apply contDiff_const
    have h := norm_iteratedFDeriv_mul_le hps hps x
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
    have hterm (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
        (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j p x‖ * ‖iteratedFDeriv ℝ (k - j) p x‖ ≤
          (if j = 0 then eta * ‖iteratedFDeriv ℝ (k + 1) (u a) x‖ else 0) +
          (if j = k then eta * ‖iteratedFDeriv ℝ (k + 1) (u a) x‖ else 0) +
          (k.choose j : ℝ) * U (j + 1) * U (k - j + 1) := by
      by_cases hj0 : j = 0
      · subst j
        have htop := mul_le_mul (hcomponent0 i a x) (hcomponent i a k x) (norm_nonneg _) heta
        have hfinal := htop.trans (le_add_of_nonneg_right
          (mul_nonneg (hU0 1) (hU0 (k + 1))))
        simpa [p, show (0 : ℕ) ≠ k by omega] using hfinal
      · by_cases hjk : j = k
        · subst j
          have hm := mul_le_mul (hcomponent i a k x) (hcomponent0 i a x)
            (abs_nonneg _) (norm_nonneg _)
          have hm' : ‖iteratedFDeriv ℝ k p x‖ * |p x| ≤
              eta * ‖iteratedFDeriv ℝ (k + 1) (u a) x‖ := by
            simpa only [p, mul_comm] using hm
          have hfinal := hm'.trans (le_add_of_nonneg_right
            (mul_nonneg (hU0 (k + 1)) (hU0 1)))
          have hzero : ‖iteratedFDeriv ℝ (k - k) p x‖ = |p x| := by
            rw [Nat.sub_self, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
          simpa [hj0, hzero] using hfinal
        · simp only [if_neg hj0, if_neg hjk, zero_add]
          have hjk' : j < k := by have := Finset.mem_range.mp hj; omega
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left ((hcomponent i a j x).trans
              (hU (j + 1) (by omega) a x)) (Nat.cast_nonneg _))
            ((hcomponent i a (k - j) x).trans (hU (k - j + 1) (by omega) a x))
            (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hU0 _))
    have hsum := Finset.sum_le_sum hterm
    simp only [Finset.sum_add_distrib] at hsum
    have hsum' : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j p x‖ * ‖iteratedFDeriv ℝ (k - j) p x‖) ≤
        eta * ‖iteratedFDeriv ℝ (k + 1) (u a) x‖ +
        eta * ‖iteratedFDeriv ℝ (k + 1) (u a) x‖ + Cq := by
      simpa using hsum
    have hf : ‖iteratedFDeriv ℝ k (fun y => (fderiv ℝ (u a) y (e i)) ^ 2) x‖ ≤
        eta * ‖iteratedFDeriv ℝ (k + 1) (u a) x‖ +
        eta * ‖iteratedFDeriv ℝ (k + 1) (u a) x‖ + Cq := by
      simpa only [pow_two, p] using h.trans hsum'
    apply hf.trans
    exact le_of_eq (by ring)
  refine ⟨Cd + (n : ℝ) * Cq + C0, by positivity, fun a x => ?_⟩
  have hsquared : ‖iteratedFDeriv ℝ k (fun y => ‖fderiv ℝ (u a) y‖ ^ 2) x‖ ≤
      (n : ℝ) * (2 * eta * ‖iteratedFDeriv ℝ (k + 1) (u a) x‖ + Cq) := by
    simp_rw [(EuclideanSpace.basisFun (Fin n) ℝ).norm_dual]
    rw [iteratedFDeriv_fun_sum_apply (fun i _ =>
      ((((hdu a).clm_apply contDiff_const).pow 2).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).contDiffAt)]
    apply (norm_sum_le _ _).trans
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hsquare i a x)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      e, EuclideanSpace.basisFun_apply] using h
  change ‖iteratedFDeriv ℝ k (fun y =>
    (fderiv ℝ (u a) y (b a y) + ‖fderiv ℝ (u a) y‖ ^ 2) + G a y (u a y)) x‖ ≤ _
  have hfg : ContDiff ℝ k (fun y => G a y (u a y)) := by
    simpa only [Function.comp_def, id_eq] using
      (((hG a).comp (contDiff_id.prodMk (hu a))).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl k))
  rw [fun_iteratedFDeriv_add_apply
    ((((hdu a).clm_apply (hb a)).add (contDiff_squared_dual_norm (hdu a))).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).contDiffAt
    hfg.contDiffAt,
    fun_iteratedFDeriv_add_apply (((hdu a).clm_apply (hb a)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).contDiffAt
      ((contDiff_squared_dual_norm (hdu a)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).contDiffAt]
  have hsum := norm_add_le_of_le (norm_add_le_of_le (hdrift a x) hsquared) (hforcing a x)
  nlinarith only [hsum]

end PoincareConjecture.M35.RadialGauge
