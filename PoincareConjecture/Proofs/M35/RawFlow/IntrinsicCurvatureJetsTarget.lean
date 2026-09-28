import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsDecay
import PoincareConjecture.Proofs.M35.RadialGauge.TargetRapidJets

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

theorem raw_intrinsic_target_jets_polynomial_decay
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
    (hrotation : ∀ t ∈ Ico 0 G.lifetime,
      ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
    {T : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime) :
    ∀ j N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 T, ∀ r ≥ 1,
      (1 + r) ^ N * |iteratedDeriv j
        (RadialGauge.smoothTargetCoupling (rawWarpingRadius P G hrotation t)) r| ≤ C := by
  let A := ↥(Icc (0 : ℝ) T)
  have ht (a : A) : a.1 ∈ Ico 0 G.lifetime := ⟨a.2.1, a.2.2.trans_lt hTlt⟩
  have hs (a : A) : ContDiff ℝ ∞ (rawWarpingRadius P G hrotation a.1) := by
    rw [rawWarpingRadius_eq P G hrotation (ht a)]
    exact intrinsicWarpingRadius_contDiff _ _ _
  have hz (a : A) : rawWarpingRadius P G hrotation a.1 0 = 0 := by
    rw [rawWarpingRadius_eq P G hrotation (ht a), intrinsicWarpingRadius_zero]
  have hb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : A) r, 1 ≤ r →
      |iteratedDeriv j (rawWarpingRadius P G hrotation a.1) r| ≤ C := by
    obtain ⟨C, hC, hCb⟩ :=
      raw_intrinsic_warping_jets_bounded_on_slab P H G hT hTlt hrotation j
    refine ⟨C, hC.le, ?_⟩
    intro a r hr
    rw [rawWarpingRadius_eq P G hrotation (ht a)]
    exact hCb a.1 a.2 r (zero_le_one.trans hr)
  have hp (j N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : A) r, 1 ≤ r →
      (1 + r) ^ N * |iteratedDeriv j (deriv (rawWarpingRadius P G hrotation a.1)) r| ≤ C := by
    obtain ⟨C, hC, hCb⟩ :=
      raw_intrinsic_slope_jets_polynomial_decay P H G hrotation hT hTlt j N
    refine ⟨C, hC.le, ?_⟩
    intro a r hr
    have hweight : (1 + r) ^ N ≤ (1 + r ^ 2) ^ N := by
      apply pow_le_pow_left₀ (by linarith) _ N
      nlinarith only [mul_nonneg (zero_le_one.trans hr) (sub_nonneg.mpr hr)]
    exact (mul_le_mul_of_nonneg_right hweight (abs_nonneg _)).trans
      (hCb a.1 a.2 r (zero_le_one.trans hr))
  intro j N
  obtain ⟨C, hC, hCb⟩ := RadialGauge.smoothTargetCoupling_rapid_jets hs hz hb hp j N
  refine ⟨C + 1, by positivity, ?_⟩
  intro t ht r hr
  exact (hCb ⟨t, ht⟩ r hr).trans (by linarith)

end PoincareConjecture.M35.Uniqueness
