import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.SpatialBounds
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.WeakDerivative.DistanceBound








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonPredecessors

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]




theorem sqrt_reducedLength_coordinates_lipschitz_ball
    {K : AncientKappaSolution n M} (P : AncientAsymptoticSolitonPredecessors K)
    (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {a : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hball : Metric.closedBall a r ⊆ e.source)
    {B : ℝ≥0} (hB : ∀ x ∈ Metric.closedBall a r, ∀ v : EuclideanSpace ℝ (Fin n),
      (K.flow.metric (0 - τ)).tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ B * ‖v‖) :
    LipschitzOnWith (Real.toNNReal (Real.sqrt (3 / τ) / 2 * B))
      (fun x => Real.sqrt (reducedLength K.flow 0 p (e x) τ)) (Metric.ball a r) := by
  obtain ⟨V⟩ := P.reduced_volume (τ + 1) (by linarith)
  obtain ⟨D⟩ := V.measure_regularity p
  let g := K.flow.metric (0 - τ)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hsmooth (x) (hx : x ∈ Metric.closedBall a r) :=
    he.contMDiffAt (e.open_source.mem_nhds (hball hx))
  have hLip : ∀ x ∈ Metric.closedBall a r, ∀ y ∈ Metric.closedBall a r,
      g.edist (e x) (e y) ≤ (B : ℝ≥0∞) * EDist.edist x y := by
    intro x hx y hy
    apply Poincare.riemannianEDist_le_mul_edist_of_convex (convex_closedBall a r)
      (fun z hz => (hsmooth z hz).of_le (by simp)) ?_ hx hy
    intro z hz
    let := normedAddCommGroupTangentSpaceVectorSpace z
    let := normedSpaceTangentSpaceVectorSpace z
    have hn : ‖mfderiv (𝓡 n) (𝓡 n) e z‖ ≤ (B : ℝ) := by
      apply ContinuousLinearMap.opNorm_le_bound _ B.coe_nonneg
      intro v
      exact hB z hz v
    exact_mod_cast hn
  have hloc := P.sqrt_reducedLength_coordinates_locallyLipschitz D hτ (by linarith)
    (fun x hx => (hsmooth x hx).continuousAt) hLip
  obtain ⟨A, hA⟩ := hloc.exists_lipschitzOnWith_of_compact (isCompact_closedBall a r)
  let G := e.source ∩ e ⁻¹' {q | (q, τ) ∈ D.regularDomain}
  have hG : IsOpen G := e.continuousOn.isOpen_inter_preimage e.open_source
    (D.regularDomain_open.preimage (continuous_id.prodMk continuous_const))
  apply Poincare.Analysis.WeakDerivative.lipschitzOnWith_of_ae_fderiv_bound_on
    volume Metric.isOpen_ball (convex_ball a r) hG.measurableSet ?_
    (hA.mono Metric.ball_subset_closedBall) ?_
  · filter_upwards [ae_regular_in_coordinates D hτ (by linarith) e he hei] with x hx hxball
    exact ⟨hball (Metric.ball_subset_closedBall hxball),
      hx (hball (Metric.ball_subset_closedBall hxball))⟩
  · intro x hx
    obtain ⟨reg⟩ := D.regular_points (e x, τ) hx.2.2
    have hc := P.regular_sqrt_reducedLength_coordinate_derivative
      (hsmooth x (Metric.ball_subset_closedBall hx.1)) reg
      (hB x (Metric.ball_subset_closedBall hx.1))
    rw [Real.coe_toNNReal _ (by positivity)]
    exact hc



theorem reducedLength_coordinates_le_center
    {K : AncientKappaSolution n M} (P : AncientAsymptoticSolitonPredecessors K)
    (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {a : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall a r ⊆ e.source)
    {B : ℝ≥0} (hB : ∀ x ∈ Metric.closedBall a r, ∀ v : EuclideanSpace ℝ (Fin n),
      (K.flow.metric (0 - τ)).tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ B * ‖v‖)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball a r) :
    reducedLength K.flow 0 p (e x) τ ≤
      (Real.sqrt (reducedLength K.flow 0 p (e a) τ) + Real.sqrt (3 / τ) / 2 * B * r) ^ 2 := by
  have hLip := P.sqrt_reducedLength_coordinates_lipschitz_ball p hτ e he hei hball hB
  have h := hLip.dist_le_mul x hx a (Metric.mem_ball_self hr)
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)] at h
  have hC : 0 ≤ Real.sqrt (3 / τ) / 2 * (B : ℝ) := by positivity
  have hbound := h.trans (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hx).le hC)
  have hsq := Real.sq_sqrt (P.reducedLength_pos p (e x) τ hτ).le
  have hupper : Real.sqrt (reducedLength K.flow 0 p (e x) τ) ≤
      Real.sqrt (reducedLength K.flow 0 p (e a) τ) + Real.sqrt (3 / τ) / 2 * B * r := by
    have := (le_abs_self _).trans hbound
    linarith
  nlinarith [Real.sqrt_nonneg (reducedLength K.flow 0 p (e x) τ)]

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
