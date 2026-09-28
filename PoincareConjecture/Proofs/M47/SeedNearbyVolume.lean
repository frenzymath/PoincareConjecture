import PoincareConjecture.Proofs.M47.SeedBallChain
import PoincareConjecture.Proofs.M36.MetricComparison









set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]




theorem seed_nearby_ball_volume
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (q z : M)
    {r d s k K : ℝ} (hr : 0 < r) (hd : 0 < d) (hdr : d ≤ r)
    (hs : 0 < s) (hsr : s ≤ 3 * r) (hk : 0 < k) (hK : 0 < K)
    (hclose : g.edist q z < ENNReal.ofReal (2 * r))
    (hcompact : IsCompact (closure (g.ball q (3 * r))))
    (hcurv : ∀ y ∈ g.ball q (3 * r), D.curvatureTensorNorm y ≤ K)
    (hvolume : ENNReal.ofReal (k * d ^ 3) ≤ calibratedMetricVolume g (g.ball z d)) :
    ENNReal.ofReal ((Real.cosh (3 * r * Real.sqrt K))⁻¹ ^ 2 *
      (k * d ^ 3 / (3 * r) ^ 3) * s ^ 3) ≤
        calibratedMetricVolume g (g.ball q s) := by
  have houter : 0 < 3 * r := mul_pos (by norm_num) hr
  have hsub : g.ball z d ⊆ g.ball q (3 * r) := by
    intro y hy
    change g.edist q y < ENNReal.ofReal (3 * r)
    have hadd := ENNReal.add_lt_add hclose hy
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * r) hd.le] at hadd
    exact ((M36.metric_edist_triangle g q z y).trans_lt hadd).trans_le
      (ENNReal.ofReal_le_ofReal (by linarith))
  let A := 3 * r * Real.sqrt K
  have hA : 0 < A := mul_pos houter (Real.sqrt_pos.mpr hK)
  have hnorm : (A / (3 * r)) ^ 2 = K := by
    dsimp only [A]
    rw [mul_div_cancel_left₀ _ houter.ne', Real.sq_sqrt hK.le]
  have hseed : 0 < k * d ^ 3 / (3 * r) ^ 3 :=
    div_pos (mul_pos hk (pow_pos hd _)) (pow_pos houter _)
  have hseedVolume : ENNReal.ofReal ((k * d ^ 3 / (3 * r) ^ 3) * (3 * r) ^ 3) ≤
      calibratedMetricVolume g (g.ball q (3 * r)) := by
    rw [div_mul_cancel₀ _ (pow_ne_zero _ houter.ne')]
    exact hvolume.trans (measure_mono hsub)
  exact M46.canonical_controlled_ball_volume g D q hA houter hs hsr hseed hcompact
    (fun y hy => (hcurv y hy).trans_eq hnorm.symm) hseedVolume



theorem seed_nearby_density_pos {r d k K : ℝ}
    (hr : 0 < r) (hd : 0 < d) (hk : 0 < k) :
    0 < (Real.cosh (3 * r * Real.sqrt K))⁻¹ ^ 2 *
      (k * d ^ 3 / (3 * r) ^ 3) :=
  mul_pos (pow_pos (inv_pos.mpr (Real.cosh_pos _)) _)
    (div_pos (mul_pos hk (pow_pos hd _)) (pow_pos (mul_pos (by norm_num) hr) _))

end PoincareConjecture.Proofs.M47
