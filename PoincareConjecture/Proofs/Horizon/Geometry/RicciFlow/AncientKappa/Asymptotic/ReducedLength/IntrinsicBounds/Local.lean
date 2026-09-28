import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.CoordinateBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Gauss.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.HausdorffDensity.ChartComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonPredecessors

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M}

theorem sqrt_reducedLength_local_intrinsic_bound
    (P : AncientAsymptoticSolitonPredecessors K) (p x : M) {τ : ℝ} (hτ : 0 < τ) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, ∀ z ∈ U,
      |Real.sqrt (reducedLength K.flow 0 p y τ) - Real.sqrt (reducedLength K.flow 0 p z τ)| ≤
        (2 * Real.sqrt (3 / τ)) * ((K.flow.metric (0 - τ)).edist y z).toReal := by
  let g := K.flow.metric (0 - τ)
  obtain ⟨e, R, hR, hsource, he0, he, hei, hcoeff⟩ :=
    g.exists_normalized_exponential_chart_bounds x (by norm_num : (0 : ℝ) < 1 / 2)
  have hnorm (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ Metric.ball 0 R)
      (v : EuclideanSpace ℝ (Fin n)) :
      ‖v‖ ≤ 2 * g.tangentNorm (e y) (mfderiv (𝓡 n) (𝓡 n) e y v) ∧
      g.tangentNorm (e y) (mfderiv (𝓡 n) (𝓡 n) e y v) ≤ 2 * ‖v‖ := by
    have hq := (hcoeff y hy).2.2 v
    have hnon : 0 ≤ g.pullbackCoefficients e y v v := by
      nlinarith [sq_nonneg ‖v‖]
    have hs := Real.sq_sqrt hnon
    change ‖v‖ ≤ 2 * Real.sqrt (g.pullbackCoefficients e y v v) ∧
      Real.sqrt (g.pullbackCoefficients e y v v) ≤ 2 * ‖v‖
    constructor <;> nlinarith [Real.sqrt_nonneg (g.pullbackCoefficients e y v v), norm_nonneg v]
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ e.source :=
    hsource (Metric.mem_ball_self hR)
  obtain ⟨V, hV, h0V, hVs, hdist⟩ := g.exists_open_distortion_of_tangentNorm_comparison
    e he hei hzero (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)))
    (by norm_num : (1 : ℝ≥0) < 2)
    (by
      filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin n)) hR] with y hy
      exact hnorm y hy)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hV.inter Metric.isOpen_ball) 0
    ⟨h0V, Metric.mem_ball_self hR⟩
  have hsmall : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (r / 2) ⊆ Metric.ball 0 r := by
    intro y hy
    change dist y 0 < r
    have hd : dist y 0 ≤ r / 2 := hy
    linarith
  have hsmallsource : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (r / 2) ⊆ e.source :=
    fun y hy => hVs (hball (hsmall hy)).1
  have hlip := P.sqrt_reducedLength_coordinates_lipschitz_ball p hτ e he hei hsmallsource
    (B := 2) (fun y hy v => (hnorm y (hball (hsmall hy)).2 v).2)
  refine ⟨e '' Metric.ball 0 (r / 2),
    e.isOpen_image_of_subset_source Metric.isOpen_ball
      (Metric.ball_subset_closedBall.trans hsmallsource), ?_, ?_⟩
  · exact ⟨0, Metric.mem_ball_self (by positivity), he0⟩
  · rintro y ⟨v, hv, rfl⟩ z ⟨w, hw, rfl⟩
    have hcoord := hlip.dist_le_mul v hv w hw
    rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)] at hcoord
    have hed := (hdist v (hball (hsmall (Metric.ball_subset_closedBall hv))).1
      w (hball (hsmall (Metric.ball_subset_closedBall hw))).1).2
    have hd : dist v w ≤ 2 * (g.edist (e v) (e w)).toReal := by
      have h := (ENNReal.toReal_le_toReal (by simp)
        (ENNReal.mul_ne_top (by norm_num) (g.edist_ne_top (e v) (e w)))).mpr hed
      simp only [ContinuousLinearEquiv.refl_apply, ENNReal.toReal_mul,
        ENNReal.coe_toReal, edist_dist, ENNReal.toReal_ofReal
          (dist_nonneg : 0 ≤ dist v w), NNReal.coe_ofNat] at h
      exact h
    norm_num only [NNReal.coe_ofNat] at hcoord
    change _ ≤ (2 * Real.sqrt (3 / τ)) * (g.edist (e v) (e w)).toReal
    exact hcoord.trans (by nlinarith [Real.sqrt_nonneg (3 / τ)])

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
