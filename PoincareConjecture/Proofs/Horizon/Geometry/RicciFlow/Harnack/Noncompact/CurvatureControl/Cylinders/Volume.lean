import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Precompact
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem volume_lower_bound_of_center_in_half_ball
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 1 ≤ n)
    (hcomplete : MetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    (p y : M) {r ρ w : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hρr : ρ ≤ r)
    (_hw : 0 ≤ w) (hy : y ∈ g.ball p (r / 2))
    (hvol : ENNReal.ofReal (w * r ^ n) ≤ g.volumeMeasure (g.ball p r)) :
    ENNReal.ofReal ((w / 2 ^ n) * ρ ^ n) ≤ g.volumeMeasure (g.ball y ρ) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hcompact : IsCompact (closure (g.ball y (3 * r))) := by
    apply (g.isCompact_closedBall_of_metricComplete hcomplete y (3 * r)).of_isClosed_subset
      isClosed_closure
    apply closure_minimal
    · exact fun x hx => (show g.edist y x < ENNReal.ofReal (3 * r) from hx).le
    · exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hbase : g.ball p r ⊆ g.ball y (2 * r) := by
    intro x hx
    have hyp : g.edist y p < ENNReal.ofReal (r / 2) := by
      change g.edist p y < ENNReal.ofReal (r / 2) at hy
      simpa only [edist, Manifold.riemannianEDist_comm] using hy
    have hsum := ENNReal.add_lt_add hyp hx
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ r / 2) hr.le] at hsum
    exact (Manifold.riemannianEDist_triangle.trans_lt hsum).trans_le
      (ENNReal.ofReal_le_ofReal (by linarith))
  have hvol' : ENNReal.ofReal (w * r ^ n) ≤ g.volumeMeasure (g.ball y (2 * r)) :=
    hvol.trans (measure_mono hbase)
  have hsmall := g.smallBall_volume_lower_bound_of_precompact_ball y hn
    (by positivity : 0 < 3 * r) (le_refl (0 : ℝ)) hcompact D
    (by intro x _ v; simpa only [mul_zero, neg_zero, zero_mul] using hRic x v)
    hρ (by linarith : ρ ≤ 2 * r) (by linarith : 2 * r < 3 * r)
  have hratio : ENNReal.ofReal (modelVolume n 0 ρ) /
      ENNReal.ofReal (modelVolume n 0 (2 * r)) = ENNReal.ofReal ((ρ / (2 * r)) ^ n) := by
    rw [← ENNReal.ofReal_div_of_pos (modelVolume_pos hn (le_refl _) (by positivity))]
    congr 1
    rw [modelVolume_zero_curvature hn, modelVolume_zero_curvature hn,
      mul_div_mul_left _ _ (euclideanUnitBallVolume_pos n).ne', div_pow]
  rw [hratio] at hsmall
  have hproduct : ENNReal.ofReal ((ρ / (2 * r)) ^ n) * ENNReal.ofReal (w * r ^ n) =
      ENNReal.ofReal ((w / 2 ^ n) * ρ ^ n) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (ρ / (2 * r)) ^ n)]
    congr 1
    rw [div_pow, mul_pow]
    field_simp
  rw [← hproduct]
  exact (mul_le_mul' le_rfl hvol').trans hsmall

end PoincareConjecture.RiemannianMetric
