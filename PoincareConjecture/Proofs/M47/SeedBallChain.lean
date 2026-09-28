import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_3_CapVolume

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

noncomputable def seedBallStepLoss (A : ℝ) : ℝ := (Real.cosh A)⁻¹ ^ 2 / 8

theorem seedBallStepLoss_bounds (A : ℝ) :
    0 < seedBallStepLoss A ∧ seedBallStepLoss A ≤ 1 := by
  have hcosh : 1 ≤ Real.cosh A := Real.one_le_cosh A
  have hi : 0 < (Real.cosh A)⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hcosh)
  have hi1 : (Real.cosh A)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).2 hcosh
  constructor
  · exact div_pos (sq_pos_of_pos hi) (by norm_num)
  · unfold seedBallStepLoss
    have hsq : (Real.cosh A)⁻¹ ^ 2 ≤ 1 := by nlinarith
    linarith

variable {M : Type u} [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem seed_ball_volume_step (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (x y : M) {A r k : ℝ} (hA : 0 < A) (hr : 0 < r) (hk : 0 < k)
    (hxy : g.edist y x < ENNReal.ofReal r)
    (hcompact : IsCompact (closure (g.ball y (2 * r))))
    (hcurv : ∀ z ∈ g.ball y (2 * r), D.curvatureTensorNorm z ≤ (A / (2 * r)) ^ 2)
    (hvolume : ENNReal.ofReal (k * r ^ 3) ≤ calibratedMetricVolume g (g.ball x r)) :
    ENNReal.ofReal (seedBallStepLoss A * k * r ^ 3) ≤
      calibratedMetricVolume g (g.ball y r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hsub : g.ball x r ⊆ g.ball y (2 * r) := by
    intro z hz
    change g.edist y z < ENNReal.ofReal (2 * r)
    rw [two_mul, ENNReal.ofReal_add hr.le hr.le]
    exact lt_of_le_of_lt Manifold.riemannianEDist_triangle (ENNReal.add_lt_add hxy hz)
  have houter : ENNReal.ofReal ((k / 8) * (2 * r) ^ 3) ≤
      calibratedMetricVolume g (g.ball y (2 * r)) := by
    rw [show (k / 8) * (2 * r) ^ 3 = k * r ^ 3 by ring]
    exact hvolume.trans (measure_mono hsub)
  have h := M46.canonical_controlled_ball_volume g D y hA (by positivity) hr
    (by linarith : r ≤ 2 * r) (div_pos hk (by norm_num)) hcompact hcurv houter
  convert h using 1
  unfold seedBallStepLoss
  congr 1
  ring

theorem seed_ball_volume_chain (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (centers : ℕ → M) (N : ℕ) {A r k : ℝ}
    (hA : 0 < A) (hr : 0 < r) (hk : 0 < k)
    (hstep : ∀ n < N, g.edist (centers (n + 1)) (centers n) < ENNReal.ofReal r)
    (hcompact : ∀ n < N, IsCompact (closure (g.ball (centers (n + 1)) (2 * r))))
    (hcurv : ∀ n < N, ∀ z ∈ g.ball (centers (n + 1)) (2 * r),
      D.curvatureTensorNorm z ≤ (A / (2 * r)) ^ 2)
    (hvolume : ENNReal.ofReal (k * r ^ 3) ≤
      calibratedMetricVolume g (g.ball (centers 0) r)) :
    ENNReal.ofReal (seedBallStepLoss A ^ N * k * r ^ 3) ≤
      calibratedMetricVolume g (g.ball (centers N) r) := by
  induction N with
  | zero => simpa only [pow_zero, one_mul] using hvolume
  | succ N ih =>
      have hbefore := ih (fun n hn => hstep n (Nat.lt_succ_of_lt hn))
        (fun n hn => hcompact n (Nat.lt_succ_of_lt hn))
        (fun n hn => hcurv n (Nat.lt_succ_of_lt hn))
      have hnext := seed_ball_volume_step g D (centers N) (centers (N + 1)) hA hr
        (mul_pos (pow_pos (seedBallStepLoss_bounds A).1 _) hk)
        (hstep N (Nat.lt_succ_self N)) (hcompact N (Nat.lt_succ_self N))
        (hcurv N (Nat.lt_succ_self N)) hbefore
      simpa only [pow_succ', mul_assoc] using hnext

theorem seed_ball_volume_chain_of_le (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (centers : ℕ → M) {N K : ℕ} (hNK : N ≤ K)
    {A r k : ℝ} (hA : 0 < A) (hr : 0 < r) (hk : 0 < k)
    (hstep : ∀ n < N, g.edist (centers (n + 1)) (centers n) < ENNReal.ofReal r)
    (hcompact : ∀ n < N, IsCompact (closure (g.ball (centers (n + 1)) (2 * r))))
    (hcurv : ∀ n < N, ∀ z ∈ g.ball (centers (n + 1)) (2 * r),
      D.curvatureTensorNorm z ≤ (A / (2 * r)) ^ 2)
    (hvolume : ENNReal.ofReal (k * r ^ 3) ≤
      calibratedMetricVolume g (g.ball (centers 0) r)) :
    ENNReal.ofReal (seedBallStepLoss A ^ K * k * r ^ 3) ≤
      calibratedMetricVolume g (g.ball (centers N) r) := by
  apply (ENNReal.ofReal_le_ofReal ?_).trans
    (seed_ball_volume_chain g D centers N hA hr hk hstep hcompact hcurv hvolume)
  have hloss := seedBallStepLoss_bounds A
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hloss.1.le hloss.2 hNK) hk.le)
    (pow_nonneg hr.le 3)

end PoincareConjecture.Proofs.M47
