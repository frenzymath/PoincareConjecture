import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Terminal.Normalization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

namespace RicciFlow

theorem scalar_monotone_terminal_of_interior
    (P : M23NormalizedKappaCompactnessPredecessors)
    {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (F : RicciFlow 3 M (Iic 0))
    (hmono : ∀ s t : ℝ, s ≤ t → t < 0 → ∀ x : M,
      (F.connection s).scalarCurvature x ≤ (F.connection t).scalarCurvature x) :
    ∀ s t : ℝ, s ≤ t → t ≤ 0 → ∀ x : M,
      (F.connection s).scalarCurvature x ≤ (F.connection t).scalarCurvature x := by
  intro s t hst ht x
  rcases lt_or_eq_of_le ht with ht | rfl
  · exact hmono s t hst ht x
  rcases lt_or_eq_of_le hst with hs | rfl
  · have hreg : ContinuousOn (fun u => (F.connection u).scalarCurvature x) (Iic 0) :=
      (P.scalar_regular M (Iic 0) F).continuousOn.comp (f := fun u : ℝ => (u, x))
        (continuous_id.prodMk continuous_const).continuousOn (fun u hu => ⟨hu, mem_univ x⟩)
    have hlim : Tendsto (fun u => (F.connection u).scalarCurvature x) (𝓝[<] 0)
        (𝓝 ((F.connection 0).scalarCurvature x)) :=
      (hreg 0 (by change (0 : ℝ) ≤ 0; exact le_refl 0)).mono Iio_subset_Iic_self
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds hs).filter_mono nhdsWithin_le_nhds] with u hu hsu
    exact hmono s u hsu.le hu x
  · exact le_rfl

theorem past_curvatureTensorNorm_le_scalar_of_nonnegative_operator
    (P : M23NormalizedKappaCompactnessPredecessors)
    {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (F : RicciFlow 3 M (Iic 0))
    (hoperator : ∀ t : ℝ, t ≤ 0 → ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hmono : ∀ s t : ℝ, s ≤ t → t ≤ 0 → ∀ x : M,
      (F.connection s).scalarCurvature x ≤ (F.connection t).scalarCurvature x)
    {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 0) (x : M) :
    |(F.connection s).curvatureTensorNorm x| ≤ (F.connection t).scalarCurvature x := by
  rw [abs_of_nonneg (show 0 ≤ (F.connection s).curvatureTensorNorm x from Real.sqrt_nonneg _)]
  exact ((F.connection s).curvatureTensorNorm_le_scalarCurvature_sharp
    (P.tensor_calculus 3 M (F.metric s) (F.connection s)) x
    (hoperator s (hst.trans ht) x)).trans (hmono s t hst ht x)

end RicciFlow

namespace NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance closedMonotonicityCarrierConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

variable {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa)
  (G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
    (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1)

private theorem closedMonotone_scalarCurvature_eq_of_metric_eq
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g h : RiemannianMetric 3 M} (D : LeviCivitaData g) (E : LeviCivitaData h)
    (heq : g = h) (x : M) : D.scalarCurvature x = E.scalarCurvature x := by
  subst h
  exact D.scalarCurvature_eq E x

theorem closedLimit_scalar_monotone
    (P : M23NormalizedKappaCompactnessPredecessors)
    (F : RicciFlow 3 G.limitCarrier.carrier (Iic 0))
    (hmetric : ∀ t : ℝ, t < 0 → F.metric t = G.limitFlow.metric (t + 1)) :
    ∀ s t : ℝ, s ≤ t → t ≤ 0 → ∀ x : G.limitCarrier.carrier,
      (F.connection s).scalarCurvature x ≤ (F.connection t).scalarCurvature x := by
  apply F.scalar_monotone_terminal_of_interior P
  intro s t hst ht x
  rw [closedMonotone_scalarCurvature_eq_of_metric_eq
    (F.connection s) (G.limitFlow.connection (s + 1)) (hmetric s (hst.trans_lt ht)) x,
    closedMonotone_scalarCurvature_eq_of_metric_eq
      (F.connection t) (G.limitFlow.connection (t + 1)) (hmetric t ht) x]
  exact S.interiorLimit_scalar_monotone G P (by linarith) (by linarith) x

theorem closedLimit_past_norm_le_scalar
    (P : M23NormalizedKappaCompactnessPredecessors)
    (F : RicciFlow 3 G.limitCarrier.carrier (Iic 0))
    (hmetric : ∀ t : ℝ, t < 0 → F.metric t = G.limitFlow.metric (t + 1))
    {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 0) (x : G.limitCarrier.carrier) :
    |(F.connection s).curvatureTensorNorm x| ≤ (F.connection t).scalarCurvature x :=
  F.past_curvatureTensorNorm_le_scalar_of_nonnegative_operator P
    (S.closedLimit_nonnegativeCurvatureOperator G P F hmetric)
    (S.closedLimit_scalar_monotone G P F hmetric) hst ht x

end NormalizedKappaSolutionSequence
end PoincareConjecture
