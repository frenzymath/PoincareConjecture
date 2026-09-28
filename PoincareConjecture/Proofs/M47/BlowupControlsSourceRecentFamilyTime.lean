import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialNativeEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff BigOperators Topology

namespace PoincareConjecture.M47

open M44

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

theorem source_recent_inverse_weight_le {u v d : ℝ}
    (hu : u ≤ 0) (hv : v ≤ 0) (hd : 0 ≤ d) (huv : |u - v| ≤ d)
    (i : Fin 3) :
    evolvingCylinderInverseWeight u i ≤ (1 + d) * evolvingCylinderInverseWeight v i := by
  have hpu : 0 < 2 * (1 - u) := by linarith
  have hpv : 0 < 2 * (1 - v) := by linarith
  have hdiff : u - v ≤ d := (le_abs_self _).trans huv
  have hprod : 2 * (1 - v) ≤ (1 + d) * (2 * (1 - u)) := by
    nlinarith only [hdiff, mul_nonneg hd (neg_nonneg.mpr hu)]
  have hinv : (2 * (1 - u))⁻¹ ≤ (1 + d) * (2 * (1 - v))⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hpu hpv]
    simpa only [one_mul] using hprod
  fin_cases i
  · exact hinv
  · exact hinv
  · change (1 : ℝ) ≤ (1 + d) * 1
    linarith

theorem source_recent_tensor_norm_time_le {u v d : ℝ}
    (hu : u ≤ 0) (hv : v ≤ 0) (hd : 0 ≤ d) (huv : |u - v| ≤ d)
    {r : ℕ} (q : UnitTwoSphere) (s : ℝ) (T : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared u (chartAt E₂ q) (chartAt E₂ q q, s) T ≤
      (1 + d) ^ r *
        roundCylinderTensorNormSquared v (chartAt E₂ q) (chartAt E₂ q q, s) T := by
  rw [evolving_roundCylinderTensorNormSquared_center (hu.trans_lt zero_lt_one),
    evolving_roundCylinderTensorNormSquared_center (hv.trans_lt zero_lt_one), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hprod := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin r)))
    (fun i _ => (M35.roundCylinderInverseWeight_pos (hu.trans_lt zero_lt_one) (a i)).le)
    (fun i _ => source_recent_inverse_weight_le hu hv hd huv (a i))
  have hprod' : (∏ i, evolvingCylinderInverseWeight u (a i)) ≤
      (1 + d) ^ r * ∏ i, evolvingCylinderInverseWeight v (a i) := by
    simpa only [evolvingCylinderInverseWeight, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] using hprod
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hprod' (sq_nonneg (T a))

noncomputable def sourceRecentTimeCorrection (u v : ℝ) (B : RoundCylinderTwoTensor) :
    RoundCylinderTwoTensor :=
  fun z a b => B z a b + EvolvingRoundCylinderMetric u z a b -
    EvolvingRoundCylinderMetric v z a b

theorem sourceRecentTimeCorrection_coefficient (u v : ℝ) (B : RoundCylinderTwoTensor)
    (c : OpenPartialHomeomorph UnitTwoSphere E₂) (p : RoundCylinderCoordinates)
    (a b : Fin 3) :
    roundCylinderTensorCoefficient (sourceRecentTimeCorrection u v B) c p a b =
      roundCylinderTensorCoefficient B c p a b + roundCylinderGram u c p a b -
        roundCylinderGram v c p a b := rfl

theorem sourceRecentTimeCorrection_smooth {epsilon u v : ℝ}
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderTensorSmoothOn epsilon B) :
    RoundCylinderTensorSmoothOn epsilon (sourceRecentTimeCorrection u v B) := by
  intro q a b
  simp only [sourceRecentTimeCorrection_coefficient]
  exact ((hB q a b).add (evolving_roundCylinderGram_contDiff u q a b).contDiffOn).sub
    (evolving_roundCylinderGram_contDiff v q a b).contDiffOn

theorem sourceRecentTimeCorrection_iteratedDerivative {u v : ℝ}
    (hu : u < 1) (hv : v < 1) (B : RoundCylinderTwoTensor) (q : UnitTwoSphere) (k : ℕ) :
    roundCylinderIteratedDerivative u (chartAt E₂ q) (sourceRecentTimeCorrection u v B) k =
      roundCylinderIteratedDerivative v (chartAt E₂ q) B k := by
  have heq : staticCylinderCorrection u (sourceRecentTimeCorrection u v B) =
      staticCylinderCorrection v B := by
    funext z a b
    simp only [staticCylinderCorrection, sourceRecentTimeCorrection]
    ring
  rw [← staticCylinderCorrection_iteratedDerivative hu, heq,
    staticCylinderCorrection_iteratedDerivative hv]

theorem exists_source_recent_time_energy_tolerance (m : ℕ) :
    ∃ d : ℝ, 0 < d ∧ ∀ {u v : ℝ}, u ≤ 0 → v ≤ 0 → |u - v| ≤ d →
      ∀ (B : RoundCylinderTwoTensor) (z : RoundCylinderSpace),
        roundCylinderJetErrorSquared u (sourceRecentTimeCorrection u v B) m z ≤
          (3 / 2 : ℝ) * roundCylinderJetErrorSquared v B m z := by
  have hnear : ∀ᶠ d : ℝ in 𝓝 0, (1 + d) ^ (m + 2) < (3 / 2 : ℝ) :=
    (show ContinuousAt (fun d : ℝ => (1 + d) ^ (m + 2)) 0 by fun_prop).eventually_lt
      continuousAt_const (by norm_num)
  obtain ⟨d0, hd0, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let d := d0 / 2
  have hd : 0 < d := half_pos hd0
  have hpower : (1 + d) ^ (m + 2) ≤ (3 / 2 : ℝ) := by
    have hmem : d ∈ Metric.ball (0 : ℝ) d0 := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hd] using
        (half_lt_self hd0)
    exact (hball hmem).le
  refine ⟨d, hd, ?_⟩
  intro u v hu hv huv B z
  unfold roundCylinderJetErrorSquared
  simp only [sourceRecentTimeCorrection_iteratedDerivative
    (hu.trans_lt zero_lt_one) (hv.trans_lt zero_lt_one)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hkm : 2 + k ≤ m + 2 := by omega
  have hfactor := (pow_le_pow_right₀ (show (1 : ℝ) ≤ 1 + d by linarith) hkm).trans hpower
  exact (source_recent_tensor_norm_time_le hu hv hd.le huv z.1 z.2 _).trans
    (mul_le_mul_of_nonneg_right hfactor
      (M35.roundCylinderTensorNormSquared_nonneg (hv.trans_lt zero_lt_one) z.1 z.2 _))

end PoincareConjecture.M47
