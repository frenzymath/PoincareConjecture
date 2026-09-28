import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.PullbackExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.MinimizingGeodesic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.MetricComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Euclidean

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

private theorem edist_le_mul_edist_of_global_tangentNorm_le
    {n : ℕ} (g h : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x v : EuclideanSpace ℝ (Fin n),
      h.tangentNorm x v ≤ C * g.tangentNorm x v) (x y : EuclideanSpace ℝ (Fin n)) :
    h.edist x y ≤ ENNReal.ofReal C * g.edist x y := by
  let r := (g.edist x y).toReal + 1
  have hr : 0 < r := by dsimp [r]; positivity
  apply edist_le_mul_edist_of_tangentNorm_le_on_ball g h x r C hr hC
    (fun z _ v => hbound z v)
  · change g.edist x x < ENNReal.ofReal r
    have hself : g.edist x x = 0 := by
      let : Bundle.RiemannianBundle
          (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
        ⟨g.toRiemannianMetric⟩
      exact Manifold.riemannianEDist_self
    rw [hself]
    exact ENNReal.ofReal_pos.mpr hr
  · change g.edist x y < ENNReal.ofReal r
    rw [← ENNReal.ofReal_toReal (g.edist_ne_top x y)]
    apply (ENNReal.ofReal_lt_ofReal_iff hr).mpr
    dsimp [r]
    linarith

@[simp] theorem euclideanMetric_edist {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    (euclideanMetric n).edist x y = EDist.edist x y :=
  (IsRiemannianManifold.out (I := 𝓡 n) x y).symm

theorem edist_bounds_of_uniform_tangentNorm_bounds
    {n : ℕ} (G : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (hbound : ∀ x v : EuclideanSpace ℝ (Fin n),
      ‖v‖ / 2 ≤ G.tangentNorm x v ∧ G.tangentNorm x v ≤ 3 * ‖v‖ / 2)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ENNReal.ofReal (‖y - x‖ / 2) ≤ G.edist x y ∧
      G.edist x y ≤ ENNReal.ofReal (3 * ‖y - x‖ / 2) := by
  have hlo := edist_le_mul_edist_of_global_tangentNorm_le G (euclideanMetric n)
    (by norm_num : (0 : ℝ) < 2) (fun x v => by
      rw [euclideanMetric_tangentNorm]
      linarith [(hbound x v).1]) x y
  have hhi := edist_le_mul_edist_of_global_tangentNorm_le (euclideanMetric n) G
    (by norm_num : (0 : ℝ) < 3 / 2) (fun x v => by
      rw [euclideanMetric_tangentNorm]
      nlinarith only [(hbound x v).2]) x y
  have he : (euclideanMetric n).edist x y = ENNReal.ofReal ‖y - x‖ := by
    rw [euclideanMetric_edist, edist_dist, dist_eq_norm, norm_sub_rev]
  rw [he] at hlo hhi
  constructor
  · rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply (ENNReal.div_le_iff (by norm_num) ENNReal.ofReal_ne_top).mpr
    simpa only [mul_comm] using hlo
  · convert hhi using 1
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    congr 1
    ring

theorem isCompact_closure_ball_of_uniform_tangentNorm_bounds
    {n : ℕ} (G : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (hbound : ∀ x v : EuclideanSpace ℝ (Fin n),
      ‖v‖ / 2 ≤ G.tangentNorm x v ∧ G.tangentNorm x v ≤ 3 * ‖v‖ / 2)
    (x : EuclideanSpace ℝ (Fin n)) (R : ℝ) :
    IsCompact (closure (G.ball x R)) := by
  have hsub : G.ball x R ⊆ Metric.closedBall x (2 * R) := by
    intro y hy
    have hd := (G.edist_bounds_of_uniform_tangentNorm_bounds hbound x y).1.trans_lt hy
    have hr : ‖y - x‖ / 2 < R :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp hd
    rw [Metric.mem_closedBall, dist_eq_norm]
    linarith
  exact (isCompact_closedBall x (2 * R)).of_isClosed_subset isClosed_closure
    (closure_minimal hsub Metric.isClosed_closedBall)

theorem exists_confined_minimizing_geodesic_of_uniform_tangentNorm_bounds
    {n : ℕ} (G : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (hbound : ∀ x v : EuclideanSpace ℝ (Fin n),
      ‖v‖ / 2 ≤ G.tangentNorm x v ∧ G.tangentNorm x v ≤ 3 * ‖v‖ / 2)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → EuclideanSpace ℝ (Fin n),
      G.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = x ∧ γ 1 = y ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        G.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * G.edist x y) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t‖ ≤ ‖x‖ + 3 * ‖y - x‖ := by
  let R := 3 * ‖y - x‖ / 2 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hy : y ∈ G.ball x R := by
    have h := (G.edist_bounds_of_uniform_tangentNorm_bounds hbound x y).2
    exact h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by
      dsimp [R]
      linarith))
  obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
    G.exists_minimizing_geodesic_of_precompact_ball x y hR
      (G.isCompact_closure_ball_of_uniform_tangentNorm_bounds hbound x R) hy
  refine ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin, ?_⟩
  intro t ht
  have hdist := hmin 0 (by simp) t ht
  rw [hγ0, zero_sub, abs_neg, abs_of_nonneg ht.1] at hdist
  have htle : ENNReal.ofReal t ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal ht.2
  have hdistle : G.edist x (γ t) ≤ G.edist x y := by
    rw [hdist]
    exact mul_le_of_le_one_left' htle
  have hlow := (G.edist_bounds_of_uniform_tangentNorm_bounds hbound x (γ t)).1
  have hhigh := (G.edist_bounds_of_uniform_tangentNorm_bounds hbound x y).2
  have hnorm : ‖γ t - x‖ / 2 ≤ 3 * ‖y - x‖ / 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hlow.trans (hdistle.trans hhigh))
  have htri := norm_add_le (γ t - x) x
  rw [sub_add_cancel] at htri
  linarith

end PoincareConjecture.RiemannianMetric
