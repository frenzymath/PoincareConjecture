import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients.DistanceLower
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Extraction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.BoundaryCoverage












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareConjecture.RiemannianMetric



theorem exists_normal_chart_overlap_limits
    {n : ℕ} {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, T3Space (M k)]
    [∀ k, PreconnectedSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)] [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (g : ∀ k, RiemannianMetric n (M k)) (q : ∀ k, ℕ → M k)
    (Φ : ∀ k, ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) (M k) ∞)
    {S r : ℝ} (hr : 0 < r) (hrS : 3 * r ≤ S)
    (hsource : ∀ k j, (Φ k j).source = Metric.ball 0 S)
    (htarget : ∀ k j, (Φ k j).target = (g k).ball (q k j) S)
    (hradial : ∀ k j x, x ∈ Metric.ball 0 S →
      (g k).edist (q k j) (Φ k j x) = ENNReal.ofReal ‖x‖)
    (helliptic : ∀ k j, ∀ x ∈ Metric.ball 0 (3 * r), ∀ v,
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ (g k).pullbackCoefficients (Φ k j) x v v ∧
      (g k).pullbackCoefficients (Φ k j) x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2)
    (hcenters : ∀ i j, ∃ A : ℝ, ∀ k, ((g k).edist (q k i) (q k j)).toReal ≤ A) :
    let X := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
    letI : Nonempty X := ⟨⟨0, Metric.mem_ball_self hr⟩⟩
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ D : ℕ → ℕ → C(X × X, ℝ),
      (∀ i j, TendstoLocallyUniformly
        (fun k (z : X × X) => ((g (σ k)).edist (Φ (σ k) i z.1) (Φ (σ k) j z.2)).toReal)
        (D i j) atTop) ∧
      ∃ T : ℕ → ℕ → OpenPartialHomeomorph X X,
        (∀ i j (x y : X), x ∈ (T i j).source ∧ T i j x = y ↔ D i j (x, y) = 0) ∧
        (∀ i, (T i i).source = univ) ∧
        (∀ i x, T i i x = x) ∧
        (∀ i j l x, x ∈ (T i j).source → T i j x ∈ (T j l).source →
          x ∈ (T i l).source ∧ T j l (T i j x) = T i l x) ∧
        (∀ i j, IsClosed {z : X × X | z.1 ∈ (T i j).source ∧ T i j z.1 = z.2}) ∧
        ∀ i j x, x ∈ (T i j).source →
          Tendsto (fun k => Function.invFun (fun z : X => Φ (σ k) j z) (Φ (σ k) i x))
            atTop (𝓝 (T i j x)) := by
  let X := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
  let : ∀ k, MetricSpace (M k) := fun k => (g k).toMetricSpace
  let : Nonempty X := ⟨⟨0, Metric.mem_ball_self hr⟩⟩
  let : LocallyCompactSpace X := Metric.isOpen_ball.locallyCompactSpace
  let e : ∀ k, ℕ → X → M k := fun k j x => Φ k j x
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ Metric.ball 0 S :=
    Metric.ball_subset_ball (by linarith)
  have hdist (k j : ℕ) (x y : X) :
      (1 / 2 : ℝ) * dist x y ≤ dist (e k j x) (e k j y) ∧
        dist (e k j x) (e k j y) ≤ (3 / 2 : ℝ) * dist x y := by
    have hh := (g k).toReal_edist_bounds_of_normal_pullback_bounds (q k j) (Φ k j)
      hr hrS (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (0 : ℝ) ≤ 9 / 4)
      (hsource k j) (htarget k j) (hradial k j) (helliptic k j) x.property y.property
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have h9 : Real.sqrt 9 = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num [Real.sqrt_div, h4, h9] at hh
    exact hh
  have hLip (k j : ℕ) : LipschitzWith (3 / 2 : ℝ≥0) (e k j) :=
    LipschitzWith.of_dist_le_mul (fun x y => by simpa using (hdist k j x y).2)
  have hopen (k j : ℕ) : Topology.IsOpenEmbedding (e k j) := by
    have hs : (X : Set (EuclideanSpace ℝ (Fin n))) ⊆ (Φ k j).source := by
      rw [hsource k j]
      exact hsub
    exact (Φ k j).toOpenPartialHomeomorph.isOpenEmbedding_restrict.comp
      (Topology.IsOpenEmbedding.inclusion hs (Metric.isOpen_ball.preimage continuous_subtype_val))
  have hconn (k : ℕ) (p : M k) (s : ℝ) : IsPreconnected (Metric.ball p s) := by
    rw [(g k).toMetricSpace_ball]
    exact (g k).isPreconnected_ball p s
  have hb (i j : ℕ) (x y : X) : ∃ B : ℝ, ∀ k, dist (e k i x) (e k j y) ≤ B := by
    obtain ⟨A, hA⟩ := hcenters i j
    refine ⟨‖(x : EuclideanSpace ℝ (Fin n))‖ + A + ‖(y : EuclideanSpace ℝ (Fin n))‖, ?_⟩
    intro k
    have hx : dist (e k i x) (q k i) = ‖(x : EuclideanSpace ℝ (Fin n))‖ := by
      rw [dist_comm]
      change ((g k).edist (q k i) (Φ k i x)).toReal = _
      rw [hradial k i x (hsub x.property),
        ENNReal.toReal_ofReal (norm_nonneg _)]
    have hy : dist (q k j) (e k j y) = ‖(y : EuclideanSpace ℝ (Fin n))‖ := by
      change ((g k).edist (q k j) (Φ k j y)).toReal = _
      rw [hradial k j y (hsub y.property), ENNReal.toReal_ofReal (norm_nonneg _)]
    calc
      dist (e k i x) (e k j y) ≤
          dist (e k i x) (q k i) + dist (q k i) (q k j) + dist (q k j) (e k j y) :=
        (dist_triangle (e k i x) (q k j) (e k j y)).trans
          (add_le_add (dist_triangle (e k i x) (q k i) (q k j)) le_rfl)
      _ ≤ ‖(x : EuclideanSpace ℝ (Fin n))‖ + A + ‖(y : EuclideanSpace ℝ (Fin n))‖ := by
        rw [hx, hy]
        exact add_le_add (add_le_add le_rfl (hA k)) le_rfl
  exact ChartDistance.exists_overlap_limits (X := fun _ => X) e (fun _ => 3 / 2) hLip
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun k j x y => (hdist k j x y).1)
    hopen hconn hb

end PoincareConjecture.RiemannianMetric
