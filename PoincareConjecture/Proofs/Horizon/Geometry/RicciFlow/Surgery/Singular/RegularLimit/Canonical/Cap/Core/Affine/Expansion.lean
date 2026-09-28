import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Affine.Comparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.RoundCylinderAffine

theorem tensorWeight_le_pow {a : ℝ} (ha : 1 ≤ a)
    {r : ℕ} (i : Fin r → Fin 3) : tensorWeight a i ≤ a ^ r := by
  calc
    tensorWeight a i ≤ ∏ _ : Fin r, a := by
      apply Finset.prod_le_prod
      · intro k _
        simp only [axisWeight]
        split <;> linarith
      · intro k _
        simp only [axisWeight]
        split <;> linarith
    _ = a ^ r := by simp

theorem tensorNorm_expansion {a u : ℝ} (ha : 1 ≤ a) (hu : u < 1)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) {r : ℕ}
    (A : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p
        (fun i => tensorWeight a i * A i) ≤
      (a ^ r) ^ 2 *
        roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p A := by
  rw [SingularRegularLimit.cylinderNorm_diagonal hu.ne,
    SingularRegularLimit.cylinderNorm_diagonal hu.ne, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hw := tensorWeight_nonneg (show 0 ≤ a by linarith) i
  have hwp := tensorWeight_le_pow ha i
  have hsq : (tensorWeight a i * A i) ^ 2 ≤ (a ^ r) ^ 2 * (A i) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right
      (show (tensorWeight a i) ^ 2 ≤ (a ^ r) ^ 2 by nlinarith) (sq_nonneg (A i))
    nlinarith
  have hweight : 0 ≤ ∏ k, SingularRegularLimit.cylinderWeight u p (i k) :=
    Finset.prod_nonneg (fun k _ => (SingularRegularLimit.cylinderWeight_pos hu p (i k)).le)
  have hh := mul_le_mul_of_nonneg_left hsq hweight
  nlinarith only [hh]

theorem tensorNorm_coordinates_eq (a s : ℝ) {u : ℝ} (hu : u ≠ 1)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) {r : ℕ}
    (A : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (coordinates a s p) A =
      roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p A := by
  rw [SingularRegularLimit.cylinderNorm_diagonal hu,
    SingularRegularLimit.cylinderNorm_diagonal hu]
  rfl

theorem normalized_rank_expansion_cost {c a : ℝ} (hca : c * a ^ 2 = 1) (k : ℕ) :
    c ^ 2 * (a ^ (2 + k)) ^ 2 = (a ^ 2) ^ k := by
  calc
    c ^ 2 * (a ^ (2 + k)) ^ 2 = (c * a ^ 2) ^ 2 * (a ^ 2) ^ k := by
      simp only [pow_add, mul_pow, ← pow_mul]
      rw [Nat.mul_comm k 2]
      ring
    _ = (a ^ 2) ^ k := by rw [hca]; simp

theorem retained_scalar_power_lower {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (hcε : 1 - c ≤ ε / 4) {k : ℕ} (hk : k ≤ ⌊(2 * ε)⁻¹⌋₊) :
    (7 / 8 : ℝ) ≤ c ^ k := by
  have hk' : (k : ℝ) ≤ (2 * ε)⁻¹ :=
    (Nat.cast_le.mpr hk).trans (Nat.floor_le (by positivity))
  have hke : (k : ℝ) * ε ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_right hk' hε.le
    have heq : (2 * ε)⁻¹ * ε = (1 / 2 : ℝ) := by field_simp
    rwa [heq] at hh
  have hkc := mul_le_mul_of_nonneg_left hcε (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hBernoulli := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ c by linarith) k
  nlinarith

theorem retained_normalized_expansion_cost_le {ε c a : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hcε : 1 - c ≤ ε / 4)
    (hca : c * a ^ 2 = 1) {k : ℕ} (hk : k ≤ ⌊(2 * ε)⁻¹⌋₊) :
    c ^ 2 * (a ^ (2 + k)) ^ 2 ≤ 8 / 7 := by
  rw [normalized_rank_expansion_cost hca]
  have hlow := retained_scalar_power_lower hε hc hcε hk
  have heq : c ^ k * (a ^ 2) ^ k = 1 := by rw [← mul_pow, hca, one_pow]
  have hn : 0 ≤ (a ^ 2) ^ k := pow_nonneg (sq_nonneg a) k
  nlinarith

theorem normalized_expansion_cost_le_of_order_deficit {c a b : ℝ}
    (hc : 0 < c) (hb : 0 < b) (hca : c * a ^ 2 = 1) (k : ℕ)
    (hdeficit : b ≤ 1 - (k : ℝ) * (1 - c)) :
    c ^ 2 * (a ^ (2 + k)) ^ 2 ≤ b⁻¹ := by
  rw [normalized_rank_expansion_cost hca]
  have hBernoulli := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ c by linarith) k
  have hlow : b ≤ c ^ k := by nlinarith
  have heq : c ^ k * (a ^ 2) ^ k = 1 := by rw [← mul_pow, hca, one_pow]
  have hn : 0 ≤ (a ^ 2) ^ k := pow_nonneg (sq_nonneg a) k
  rw [← one_div]
  apply (le_div_iff₀ hb).2
  nlinarith [mul_le_mul_of_nonneg_right hlow hn]

theorem retained_normalized_expansion_cost_le_half {ε c a : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hcε : 1 - c ≤ ε / 2)
    (hca : c * a ^ 2 = 1) {k : ℕ} (hk : k ≤ ⌊(2 * ε)⁻¹⌋₊) :
    c ^ 2 * (a ^ (2 + k)) ^ 2 ≤ 4 / 3 := by
  have hk' : (k : ℝ) ≤ (2 * ε)⁻¹ :=
    (Nat.cast_le.mpr hk).trans (Nat.floor_le (by positivity))
  have hke : (k : ℝ) * ε ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_right hk' hε.le
    have heq : (2 * ε)⁻¹ * ε = (1 / 2 : ℝ) := by field_simp
    rwa [heq] at hh
  have hkc := mul_le_mul_of_nonneg_left hcε (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hdeficit : (3 / 4 : ℝ) ≤ 1 - (k : ℝ) * (1 - c) := by nlinarith
  simpa using normalized_expansion_cost_le_of_order_deficit hc
    (by norm_num : (0 : ℝ) < 3 / 4) hca k hdeficit

theorem errorPullback_jetError_expansion_le {ε c a : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hcε : 1 - c ≤ ε / 2)
    (ha : 1 ≤ a) (hca : c * a ^ 2 = 1) (s : ℝ)
    (B : RoundCylinderTwoTensor)
    (hB : ∀ (z : RoundCylinderSpace) (c d : ℝ) (v w : RoundCylinderTangent z),
      B z (c • v) (d • w) = c * d * B z v w)
    (order : ℕ) (horder : order ≤ ⌊(2 * ε)⁻¹⌋₊) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared 0 (errorPullback c a s B) order z ≤
      (4 / 3) * roundCylinderJetErrorSquared 0 B order (space a s z) := by
  unfold roundCylinderJetErrorSquared
  dsimp only [space]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [iteratedDerivative_errorPullback c a s (by linarith : a ≠ 0) B hB]
  rw [SingularRegularLimit.cylinderNorm_smul (by norm_num : (0 : ℝ) ≠ 1)]
  let q := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let p : RoundCylinderCoordinates := (q z.1, z.2)
  let A := roundCylinderIteratedDerivative 0 q B k (coordinates a s p)
  have hexp := tensorNorm_expansion ha (by norm_num : (0 : ℝ) < 1) z.1 p A
  have hcost := retained_normalized_expansion_cost_le_half hε hc hcε hca
    ((Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans horder)
  have hn : 0 ≤ roundCylinderTensorNormSquared 0 q p A := by
    rw [SingularRegularLimit.cylinderNorm_diagonal (by norm_num : (0 : ℝ) ≠ 1)]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg
      (Finset.prod_nonneg (fun j _ =>
        (SingularRegularLimit.cylinderWeight_pos (by norm_num : (0 : ℝ) < 1) p (i j)).le))
      (sq_nonneg _))
  change _ ≤ (4 / 3) * roundCylinderTensorNormSquared 0 q (coordinates a s p) A
  rw [tensorNorm_coordinates_eq a s (by norm_num : (0 : ℝ) ≠ 1)]
  exact (mul_le_mul_of_nonneg_left hexp (sq_nonneg c)).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcost hn)

theorem normalized_jetError_expansion_weighted_le {ε δ c a : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hcε : 1 - c ≤ ε / 2)
    (ha : 1 ≤ a) (hca : c * a ^ 2 = 1) (s : ℝ)
    (B : RoundCylinderTwoTensor) (hB : RoundCylinderTensorSmoothOn ε B)
    (hbilinear : ∀ (z : RoundCylinderSpace) (c d : ℝ) (v w : RoundCylinderTangent z),
      B z (c • v) (d • w) = c * d * B z v w)
    (hsub : MapsTo (fun t : ℝ => a * t + s)
      (Ioo (-δ⁻¹) δ⁻¹) (Ioo (-ε⁻¹) ε⁻¹))
    (order : ℕ) (horder : order ≤ ⌊(2 * ε)⁻¹⌋₊)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-δ⁻¹) δ⁻¹)
    {θ : ℝ} (hθ : 0 < θ) :
    θ * roundCylinderJetErrorSquared 0 (fun z v w => c * pullback a s B z v w)
        order z ≤
      θ * (1 + θ) * (2 * (c - 1) ^ 2) +
        (1 + θ) * (4 / 3) * roundCylinderJetErrorSquared 0 B order (space a s z) := by
  have hs := smoothOn_scaled_pullback c a s hB hbilinear hsub
  have hm : RoundCylinderTensorSmoothOn δ
      (fun z v w => c * pullback a s (EvolvingRoundCylinderMetric 0) z v w) := by
    rw [scaled_model_pullback hca]
    intro q i j
    exact (contDiff_roundCylinderGram _ q i j).contDiffOn
  have heq : TerminalNeck.cylinderDifference 0
      (fun z v w => c * pullback a s B z v w)
      (fun z v w => c * pullback a s (EvolvingRoundCylinderMetric 0) z v w) =
        errorPullback c a s B := by
    funext z v w
    dsimp only [TerminalNeck.cylinderDifference, errorPullback]
    ring
  have hh := TerminalNeck.cylinderDifference_jetError_weighted_le
    (by norm_num : (0 : ℝ) < 1) _ _ hs hm order z hz hθ
  rw [heq, scaled_model_jetError hca (by norm_num : (0 : ℝ) ≠ 1)] at hh
  simp only [sub_zero, mul_one, div_one] at hh
  apply hh.trans
  apply add_le_add_right
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (errorPullback_jetError_expansion_le hε hc hcε ha hca s B hbilinear order horder z)
    (show 0 ≤ 1 + θ by linarith)

theorem close_normalized_expanding_pullback {ε c a : ℝ} (hε : 0 < ε)
    (hc : 0 < c) (hcone : c ≤ 1) (hcε : 1 - c ≤ ε / 2)
    (ha : 1 ≤ a) (hca : c * a ^ 2 = 1) (s : ℝ)
    (B : RoundCylinderTwoTensor) (hB : RoundCylinderClose ε 0 B)
    (hbilinear : ∀ (z : RoundCylinderSpace) (c d : ℝ) (v w : RoundCylinderTangent z),
      B z (c • v) (d • w) = c * d * B z v w)
    (hsub : MapsTo (fun t : ℝ => a * t + s)
      (Ioo (-(2 * ε)⁻¹) (2 * ε)⁻¹) (Ioo (-ε⁻¹) ε⁻¹)) :
    RoundCylinderClose (2 * ε) 0 (fun z v w => c * pullback a s B z v w) := by
  refine ⟨smoothOn_scaled_pullback c a s hB.1 hbilinear hsub,
    (7 / 2) * ε ^ 2, by nlinarith [sq_pos_of_pos hε], ?_⟩
  intro z hz
  have horder : ⌊(2 * ε)⁻¹⌋₊ ≤ ⌊ε⁻¹⌋₊ :=
    Nat.floor_mono ((inv_le_inv₀ (by positivity) hε).2 (by linarith))
  have hold : roundCylinderJetErrorSquared 0 B ⌊(2 * ε)⁻¹⌋₊ (space a s z) ≤ ε ^ 2 :=
    (DeepHorn.evolvingCylinderJetErrorSquared_mono (by norm_num) B _ horder).trans
      ((hB.2.choose_spec.2 _ (hsub hz)).trans hB.2.choose_spec.1.le)
  have hweighted := normalized_jetError_expansion_weighted_le hε hc hcε ha hca s
    B hB.1 hbilinear hsub ⌊(2 * ε)⁻¹⌋₊ le_rfl z hz (by norm_num : (0 : ℝ) < 2)
  have hsmall : (c - 1) ^ 2 ≤ (ε / 2) ^ 2 := by nlinarith
  nlinarith

theorem close_normalized_pullback_of_abs {ε c a : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 200) (hc : 0 < c)
    (hcε : |c - 1| ≤ ε / 2) (ha : 0 < a) (hca : c * a ^ 2 = 1) (s : ℝ)
    (B : RoundCylinderTwoTensor) (hB : RoundCylinderClose ε 0 B)
    (hbilinear : ∀ (z : RoundCylinderSpace) (c d : ℝ) (v w : RoundCylinderTangent z),
      B z (c • v) (d • w) = c * d * B z v w)
    (hsub : MapsTo (fun t : ℝ => a * t + s)
      (Ioo (-(2 * ε)⁻¹) (2 * ε)⁻¹) (Ioo (-ε⁻¹) ε⁻¹)) :
    RoundCylinderClose (2 * ε) 0 (fun z v w => c * pullback a s B z v w) := by
  obtain ⟨hlow, hhigh⟩ := abs_le.mp hcε
  rcases le_total 1 c with hcone | hcone
  · have haone : a ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
    refine ⟨smoothOn_scaled_pullback c a s hB.1 hbilinear hsub,
      (7 / 2) * ε ^ 2, by nlinarith [sq_pos_of_pos hε], ?_⟩
    intro z hz
    have horder : ⌊(2 * ε)⁻¹⌋₊ ≤ ⌊ε⁻¹⌋₊ :=
      Nat.floor_mono ((inv_le_inv₀ (by positivity) hε).2 (by linarith))
    have hold : roundCylinderJetErrorSquared 0 B ⌊(2 * ε)⁻¹⌋₊ (space a s z) ≤ ε ^ 2 :=
      (DeepHorn.evolvingCylinderJetErrorSquared_mono (by norm_num) B _ horder).trans
        ((hB.2.choose_spec.2 _ (hsub hz)).trans hB.2.choose_spec.1.le)
    have hweighted := normalized_jetError_weighted_le ha haone hca s B hB.1 hbilinear
      hsub ⌊(2 * ε)⁻¹⌋₊ z hz (by norm_num : (0 : ℝ) < 2)
    have hsmall : (c - 1) ^ 2 ≤ (ε / 2) ^ 2 := by nlinarith
    have hcmax : c ≤ 11 / 10 := by linarith
    have hscalar : c ^ 2 ≤ (121 / 100 : ℝ) := by nlinarith
    have hcost := (mul_le_mul_of_nonneg_left hold (sq_nonneg c)).trans
      (mul_le_mul_of_nonneg_right hscalar (sq_nonneg ε))
    nlinarith
  · have haone : 1 ≤ a := by nlinarith [sq_nonneg (a - 1)]
    exact close_normalized_expanding_pullback hε hc hcone (by linarith) haone hca
      s B hB hbilinear hsub

end PoincareConjecture.RoundCylinderAffine
