import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsTarget
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsVelocityBound
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsTailFloor
import PoincareConjecture.Proofs.M35.RadialGauge.FullForcingPolynomialBounds










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

open RadialGauge

variable (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
  (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
  (hrotation : ∀ t ∈ Ico 0 G.lifetime,
    ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
      (G.flow.metric t).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
  {T : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime)

include H hT hTlt

private theorem exterior_target_jets (j N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 T, ∀ r ≥ 1,
      (1 + r) ^ N * |iteratedDeriv j
        (radialTargetCoupling (rawWarpingRadius P G hrotation t)) r| ≤ C := by
  obtain ⟨C, hC, hCb⟩ := raw_intrinsic_target_jets_polynomial_decay
    P H G hrotation hT hTlt j N
  refine ⟨C, hC, ?_⟩
  intro t ht r hr
  have htG : t ∈ Ico 0 G.lifetime := ⟨ht.1, ht.2.trans_lt hTlt⟩
  have hf : ContDiff ℝ ∞ (rawWarpingRadius P G hrotation t) := by
    rw [rawWarpingRadius_eq P G hrotation htG]
    exact intrinsicWarpingRadius_contDiff _ _ _
  have hf0 : rawWarpingRadius P G hrotation t 0 = 0 := by
    rw [rawWarpingRadius_eq P G hrotation htG, intrinsicWarpingRadius_zero]
  have heq : smoothTargetCoupling (rawWarpingRadius P G hrotation t) =ᶠ[𝓝 r]
      radialTargetCoupling (rawWarpingRadius P G hrotation t) := by
    filter_upwards [eventually_gt_nhds (lt_of_lt_of_le zero_lt_one hr)] with s hs
    exact smoothTargetCoupling_eq_exterior hf hf0 hs.ne'
  rw [← heq.iteratedDeriv_eq j]
  exact hCb t ht r hr



theorem raw_intrinsic_forcing_weighted_value :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 T, ∀ t₀ ∈ Icc 0 T, ∀ r ≥ 1,
      (1 + r) * |radialGaugeForcing (rawWarpingRadius P G hrotation t)
        (rawWarpingRadius P G hrotation t₀) (rawRadialVelocity P G hrotation t) 0 r| ≤ C := by
  obtain ⟨V, hV, hVb⟩ := raw_intrinsic_velocity_jets_bounded_on_slab
    P H G hrotation hT hTlt 0
  simp only [iteratedDeriv_zero] at hVb
  obtain ⟨C, hC, hCb⟩ := exterior_target_jets P H G hrotation hT hTlt 0 1
  simp only [iteratedDeriv_zero, pow_one] at hCb
  obtain ⟨c, hc, hfloor⟩ := raw_intrinsic_warping_tail_floor P G hrotation hT.le hTlt
  refine ⟨4 + 2 * V + 2 * C / c ^ 2, by positivity, ?_⟩
  intro t ht t₀ ht₀ r hr
  have htG : t ∈ Ico 0 G.lifetime := ⟨ht.1, ht.2.trans_lt hTlt⟩
  have hcontrols := raw_intrinsic_warping_controls P H G htG (hrotation t htG)
    r (lt_of_lt_of_le zero_lt_one hr)
  rw [← rawWarpingRadius_eq P G hrotation htG] at hcontrols
  exact radialGaugeForcing_weighted_value_bound hr hc (hfloor t ht r hr)
    hcontrols.2.2.1 hcontrols.2.2.2.2.2 (hVb t ht r (zero_le_one.trans hr)) (hCb t₀ ht₀ r hr)




theorem raw_intrinsic_forcing_weighted_radial_derivative {eta : ℝ} :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 T, ∀ t₀ ∈ Icc 0 T, ∀ r sigma,
      max 1 (Real.exp eta) ≤ r → |sigma| ≤ eta →
      (1 + r) * |deriv (radialGaugeForcing (rawWarpingRadius P G hrotation t)
        (rawWarpingRadius P G hrotation t₀) (rawRadialVelocity P G hrotation t) sigma) r| ≤
        C / r := by
  obtain ⟨V, hV, hVb⟩ := raw_intrinsic_velocity_jets_bounded_on_slab
    P H G hrotation hT hTlt 0
  simp only [iteratedDeriv_zero] at hVb
  obtain ⟨C₀, hC₀, hC₀b⟩ := exterior_target_jets P H G hrotation hT hTlt 0 1
  obtain ⟨C₁, hC₁, hC₁b⟩ := exterior_target_jets P H G hrotation hT hTlt 1 2
  simp only [iteratedDeriv_zero, pow_one] at hC₀b
  simp only [iteratedDeriv_one] at hC₁b
  obtain ⟨c, hc, hfloor⟩ := raw_intrinsic_warping_tail_floor P G hrotation hT.le hTlt
  refine ⟨8 + 2 * V + Real.exp eta * (4 * C₁ + 8 * C₀) / c ^ 2, by positivity, ?_⟩
  intro t ht t₀ ht₀ r sigma hr hsigma
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hrstrip : Real.exp eta ≤ r := (le_max_right _ _).trans hr
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have htG : t ∈ Ico 0 G.lifetime := ⟨ht.1, ht.2.trans_lt hTlt⟩
  have ht₀G : t₀ ∈ Ico 0 G.lifetime := ⟨ht₀.1, ht₀.2.trans_lt hTlt⟩
  have hf : ContDiff ℝ ∞ (rawWarpingRadius P G hrotation t) := by
    rw [rawWarpingRadius_eq P G hrotation htG]
    exact intrinsicWarpingRadius_contDiff _ _ _
  have hf₀ : ContDiff ℝ ∞ (rawWarpingRadius P G hrotation t₀) := by
    rw [rawWarpingRadius_eq P G hrotation ht₀G]
    exact intrinsicWarpingRadius_contDiff _ _ _
  have hcontrols := raw_intrinsic_warping_controls P H G htG (hrotation t htG) r hrp
  rw [← rawWarpingRadius_eq P G hrotation htG] at hcontrols
  have hvd : HasDerivAt (rawRadialVelocity P G hrotation t)
      (2 * deriv (deriv (rawWarpingRadius P G hrotation t)) r /
        rawWarpingRadius P G hrotation t r) r := by
    rw [rawRadialVelocity_eq P G hrotation htG, rawWarpingRadius_eq P G hrotation htG]
    have h := intrinsicRadialVelocity_hasDerivAt (G.flow.metric t)
      (hrotation t htG) (G.complete P htG) r
    rwa [intrinsicRadialAcceleration_eq _ _ _ hrp] at h
  have hexp : 1 ≤ Real.exp eta * Real.exp sigma := by
    rw [← Real.exp_add, Real.one_le_exp_iff]
    linarith only [neg_le_of_abs_le hsigma]
  have hq : 1 ≤ r * Real.exp sigma := hexp.trans
    (mul_le_mul_of_nonneg_right hrstrip (Real.exp_pos sigma).le)
  exact radialGaugeForcing_weighted_derivative_inverse_radius hf hf₀ hr1 hrstrip hsigma
    hc (hfloor t ht r hr1) hcontrols.2.2.1 hcontrols.2.2.2.2.2
    (hVb t ht r (zero_le_one.trans hr1)) hvd
    (hC₀b t₀ ht₀ _ hq) (hC₁b t₀ ht₀ _ hq)

end PoincareConjecture.M35.Uniqueness
