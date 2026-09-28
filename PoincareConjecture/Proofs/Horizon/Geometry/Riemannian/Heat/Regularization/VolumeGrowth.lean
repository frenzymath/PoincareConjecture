import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.VolumeGrowth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bounds.Ricci

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M]

theorem exists_exponential_volume_bound_of_abs_sectionalCurvature_le
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hn : 1 ≤ n) (hcomplete : MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ x v w, |D.sectionalCurvature x v w| ≤ K) (O : M) :
    ∃ V c : ℝ, 0 ≤ V ∧ ∀ R : ℝ, 1 ≤ R →
      (g.volumeMeasure {x | (g.edist O x).toReal ≤ R}).toReal ≤
        V * Real.exp (c * R) := by
  let B : ℝ := (n - 1 : ℕ) * Real.sqrt K
  refine ⟨2 ^ n * g.volumeMeasure.real (g.ball O 1), (n : ℝ) + 2 * B,
    mul_nonneg (by positivity) ENNReal.toReal_nonneg, ?_⟩
  intro R hR
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRic : ∀ x v, -(((n : ℝ) - 1) * K) * g.inner x v v ≤ D.ricci x v v := by
    intro x v
    simpa only [neg_mul] using
      D.ricci_quadratic_lower_bound_of_abs_sectionalCurvature_le x K (hsec x) v
  have hgrowth := g.volumeMeasure_ball_growth_of_ricci D hn hcomplete hK hRic O
    (r := 1) (R := 2 * R) zero_lt_one (by linarith)
  have hsub : {x | (g.edist O x).toReal ≤ R} ⊆ g.ball O (2 * R) := by
    intro x hx
    change g.edist O x < ENNReal.ofReal (2 * R)
    rw [ENNReal.lt_ofReal_iff_toReal_lt (g.edist_ne_top O x)]
    exact lt_of_le_of_lt hx (by linarith)
  have hmeasure : (g.volumeMeasure {x | (g.edist O x).toReal ≤ R}).toReal ≤
      g.volumeMeasure.real (g.ball O (2 * R)) :=
    ENNReal.toReal_mono (g.volumeMeasure_ball_lt_top hcomplete O (2 * R)).ne
      (measure_mono hsub)
  have hpow : R ^ n ≤ Real.exp ((n : ℝ) * R) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hR0.le (le_trans (by linarith : R ≤ R + 1)
      (Real.add_one_le_exp R)) n
  calc
    _ ≤ g.volumeMeasure.real (g.ball O (2 * R)) := hmeasure
    _ ≤ (2 * R) ^ n * Real.exp (B * (2 * R)) *
        g.volumeMeasure.real (g.ball O 1) := by
      simpa only [div_one, B, mul_assoc] using hgrowth
    _ ≤ (2 ^ n * Real.exp ((n : ℝ) * R)) * Real.exp (B * (2 * R)) *
        g.volumeMeasure.real (g.ball O 1) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by positivity)) (Real.exp_pos _).le)
        ENNReal.toReal_nonneg
    _ = _ := by
      rw [show ((n : ℝ) + 2 * B) * R = (n : ℝ) * R + B * (2 * R) by ring,
        Real.exp_add]
      ring

end PoincareConjecture.RiemannianMetric
