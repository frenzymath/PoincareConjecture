import PoincareConjecture.Proofs.Ch01.CurvatureConnection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.ScalarBuffer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Monotonicity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

private theorem terminal_scalarCurvature_eq_of_metric_eq
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g h : RiemannianMetric n M} (D : LeviCivitaData g) (E : LeviCivitaData h)
    (heq : g = h) (x : M) : D.scalarCurvature x = E.scalarCurvature x := by
  subst h
  exact D.scalarCurvature_eq E x

private theorem terminal_nonnegativeCurvatureOperator_iff_of_metric_eq
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g h : RiemannianMetric n M} (D : LeviCivitaData g) (E : LeviCivitaData h)
    (heq : g = h) (x : M) :
    D.NonnegativeCurvatureOperator x ↔ E.NonnegativeCurvatureOperator x := by
  subst h
  simp only [LeviCivitaData.NonnegativeCurvatureOperator,
    LeviCivitaData.curvatureOperatorQuadratic, D.horizon_curvatureTensor_eq E]

namespace RicciFlow




theorem nonnegativeCurvatureOperator_terminal_of_interior
    (P : M23NormalizedKappaCompactnessPredecessors)
    {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (F : RicciFlow 3 M (Iic 0))
    (hoperator : ∀ t : ℝ, t < 0 → ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x) (x : M) :
    (F.connection 0).NonnegativeCurvatureOperator x := by
  classical
  intro A hA
  let e := (F.metric 0).orthonormalBasis x
  have hquad : Tendsto (fun t : ℝ => ∑ a, ∑ b, ∑ c, ∑ d,
      A a b * A c d * (F.connection t).curvatureTensor x (e a) (e b) (e c) (e d))
      (𝓝[<] 0) (𝓝 ((F.connection 0).curvatureOperatorQuadratic x A)) := by
    unfold LeviCivitaData.curvatureOperatorQuadratic
    apply tendsto_finsetSum
    intro a _
    apply tendsto_finsetSum
    intro b _
    apply tendsto_finsetSum
    intro c _
    apply tendsto_finsetSum
    intro d _
    exact tendsto_const_nhds.mul
      ((P.curvature_evolution M (Iic 0) F 0 (by change (0 : ℝ) ≤ 0; exact le_refl 0)
        x (e a) (e b) (e c) (e d)).continuousWithinAt.mono
        Iio_subset_Iic_self)
  apply ge_of_tendsto hquad
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (F.connection t).curvatureOperator_nonneg_in_frame x (hoperator t ht x) e A hA

end RicciFlow

namespace NormalizedKappaSolutionSequence

variable {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa)

local instance normalizationSourceConnected (k : ℕ) :
    ConnectedSpace (S.term k).carrier.carrier := (S.term k).connectedSpace

variable (G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
  (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1)




theorem closedLimit_scalar_normalized
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (F : RicciFlow 3 G.limitCarrier.carrier (Iic 0))
    (hmetric : ∀ t : ℝ, t < 0 → F.metric t = G.limitFlow.metric (t + 1)) :
    (F.connection 0).scalarCurvature G.base = 1 := by
  obtain ⟨D, _, hD⟩ := S.exists_base_scalar_time_constant P hcontrol
  have htendsto (t : ℝ) (ht : t < 0) :
      Tendsto (fun k => ((S.term (G.subsequence k)).flow.flow.connection t).scalarCurvature
        (S.term (G.subsequence k)).base) atTop
        (𝓝 ((F.connection t).scalarCurvature G.base)) := by
    have h := S.interiorLimit_tendsto_scalarCurvature G (t + 1) (by linarith) G.base
    rw [← terminal_scalarCurvature_eq_of_metric_eq
      (F.connection t) (G.limitFlow.connection (t + 1)) (hmetric t ht) G.base] at h
    have hshift : t + 1 - 1 = t := by ring
    change Tendsto (fun k => ((S.term (G.subsequence k)).flow.flow.connection
      (t + 1 - 1)).scalarCurvature (G.embedding k G.base)) atTop
        (𝓝 ((F.connection t).scalarCurvature G.base)) at h
    rw [hshift] at h
    simpa only [G.base_preserving] using h
  have hupper (t : ℝ) (ht : t < 0) : (F.connection t).scalarCurvature G.base ≤ 1 := by
    apply le_of_tendsto (htendsto t ht)
    exact Eventually.of_forall fun k => by
      have h := P.scalar_monotone (S.term (G.subsequence k)).carrier.carrier
        (S.term (G.subsequence k)).flow t 0 ht.le le_rfl (S.term (G.subsequence k)).base
      simpa only [(S.term (G.subsequence k)).scalar_normalized] using h
  have hlower (t : ℝ) (ht : t < 0) :
      1 - D * (0 - t) ≤ (F.connection t).scalarCurvature G.base := by
    apply ge_of_tendsto (htendsto t ht)
    exact Eventually.of_forall fun k => by linarith [hD (G.subsequence k) t ht.le]
  have hreg : ContinuousOn (fun t => (F.connection t).scalarCurvature G.base) (Iic 0) :=
    (P.scalar_regular G.limitCarrier.carrier (Iic 0) F).continuousOn.comp
      (f := fun t : ℝ => (t, G.base))
      (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨ht, mem_univ _⟩)
  have hzero : (0 : ℝ) ∈ closure (Iio (0 : ℝ)) := by simp
  apply le_antisymm
  · exact le_on_closure (s := Iio (0 : ℝ)) hupper (by simpa only [closure_Iio] using hreg)
      continuousOn_const hzero
  · have h := le_on_closure (s := Iio (0 : ℝ)) hlower
      (continuous_const.sub (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
      (by simpa only [closure_Iio] using hreg) hzero
    simpa only [sub_self, mul_zero, sub_zero] using h



theorem closedLimit_nonnegativeCurvatureOperator
    (P : M23NormalizedKappaCompactnessPredecessors)
    (F : RicciFlow 3 G.limitCarrier.carrier (Iic 0))
    (hmetric : ∀ t : ℝ, t < 0 → F.metric t = G.limitFlow.metric (t + 1)) :
    ∀ t : ℝ, t ≤ 0 → ∀ x : G.limitCarrier.carrier,
      (F.connection t).NonnegativeCurvatureOperator x := by
  have hinterior (t : ℝ) (ht : t < 0) (x : G.limitCarrier.carrier) :
      (F.connection t).NonnegativeCurvatureOperator x :=
    (terminal_nonnegativeCurvatureOperator_iff_of_metric_eq
      (F.connection t) (G.limitFlow.connection (t + 1)) (hmetric t ht) x).mpr
      (S.interiorLimit_nonnegativeCurvatureOperator G (t + 1) (by linarith) x)
  intro t ht x
  rcases lt_or_eq_of_le ht with ht | rfl
  · exact hinterior t ht x
  · exact F.nonnegativeCurvatureOperator_terminal_of_interior P hinterior x

end NormalizedKappaSolutionSequence
end PoincareConjecture
