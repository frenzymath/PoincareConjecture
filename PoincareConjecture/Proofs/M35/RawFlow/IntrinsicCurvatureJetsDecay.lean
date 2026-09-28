import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsBounds
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicPolynomialDecay
import PoincareConjecture.Proofs.M35.RadialGauge.PolynomialJetDecay











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

variable (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
  (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
  (hrotation : ∀ t ∈ Ico 0 G.lifetime,
    ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
      (G.flow.metric t).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)

include H



theorem raw_intrinsic_slope_jets_polynomial_decay {T : ℝ} (hT : 0 < T)
    (hTlt : T < G.lifetime) :
    ∀ j N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 T, ∀ r ≥ 0,
      (1 + r ^ 2) ^ N * |iteratedDeriv j (rawWarpingSlope P G hrotation t) r| ≤ C := by
  let A := ↥(Icc (0 : ℝ) T)
  have ht (a : A) : a.1 ∈ Ico 0 G.lifetime := ⟨a.2.1, a.2.2.trans_lt hTlt⟩
  have hs (a : A) : ContDiff ℝ ∞ (rawWarpingSlope P G hrotation a.1) :=
    rawWarpingSlope_contDiff P G hrotation (ht a)
  have hjets (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : A) r, 0 ≤ r →
      |iteratedDeriv j (rawWarpingSlope P G hrotation a.1) r| ≤ C := by
    obtain ⟨C, hC, hCb⟩ :=
      raw_intrinsic_warping_jets_bounded_on_slab P H G hT hTlt hrotation (j + 1)
    refine ⟨C, hC.le, ?_⟩
    intro a r hr
    change |iteratedDeriv j (deriv (rawWarpingRadius P G hrotation a.1)) r| ≤ C
    rw [← iteratedDeriv_succ', rawWarpingRadius_eq P G hrotation (ht a)]
    exact hCb a.1 a.2 r hr
  have hvalue (N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : A) r, 0 ≤ r →
      (1 + r ^ 2) ^ N * |rawWarpingSlope P G hrotation a.1 r| ≤ C := by
    obtain ⟨C, hC, hCb⟩ := raw_intrinsic_slope_polynomial_decay P H G hrotation hT hTlt N
    refine ⟨C, hC.le, ?_⟩
    intro a r hr
    rw [abs_of_nonneg (rawWarpingSlope_bounds P G hrotation (ht a) hr).1]
    exact hCb a.1 a.2 r hr
  intro j N
  obtain ⟨C, hC, hCb⟩ := RadialGauge.polynomial_iteratedDeriv_bounds hs hjets hvalue j N
  refine ⟨C + 1, by positivity, ?_⟩
  intro t ht r hr
  exact (hCb ⟨t, ht⟩ r hr).trans (by linarith)



theorem raw_intrinsic_warping_jets_polynomial_decay {T : ℝ} (hT : 0 < T)
    (hTlt : T < G.lifetime) :
    ∀ j N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 T, ∀ r ≥ 0,
      (1 + r ^ 2) ^ N * |iteratedDeriv (j + 1) (rawWarpingRadius P G hrotation t) r| ≤ C := by
  intro j N
  obtain ⟨C, hC, hCb⟩ :=
    raw_intrinsic_slope_jets_polynomial_decay P H G hrotation hT hTlt j N
  refine ⟨C, hC, ?_⟩
  intro t ht r hr
  rw [iteratedDeriv_succ']
  exact hCb t ht r hr

end PoincareConjecture.M35.Uniqueness
