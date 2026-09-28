import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.Persistence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.Main
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity
import PoincareConjecture.Statements.M32HornSelection

set_option autoImplicit false

universe u

namespace PoincareConjecture.M32

open Set
open RiemannianMetric
open scoped Manifold ContDiff Bundle ENNReal Topology

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

theorem blowupLimit_busemann_persists_on_closed_slab
    (P : RepairedHornSelectionPredecessors.{u}) {T₀ : ℝ≥0∞}
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval T₀))
    {T : ℝ} (hT : 0 < T) (hsub : Icc (-T) 0 ⊆ blowupBackwardInterval T₀)
    (γ : ℝ → L.carrier.carrier)
    (hγ : ∀ s t : ℝ,
      (L.flow.metric 0).edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    let f := (L.flow.metric 0).busemann γ
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f ∧ f (γ 0) = 0 ∧
      ∀ t ∈ Icc (-T) 0,
        (L.flow.connection t).gradient f = (L.flow.connection 0).gradient f ∧
          HasUnitGradient (L.flow.connection t) f ∧
            HasZeroHessian (L.flow.connection t) f := by
  let : ConnectedSpace L.carrier.carrier := L.connectedSpace
  let f := (L.flow.metric 0).busemann γ
  have hneg : -T < 0 := by linarith
  have hnontrivial : (Icc (-T) (0 : ℝ)).Nontrivial :=
    ⟨-T, ⟨le_rfl, hneg.le⟩, 0, ⟨hneg.le, le_rfl⟩, hneg.ne⟩
  let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow
    L.flow hsub ordConnected_Icc hnontrivial
  have hc : ∀ t ∈ Icc (-T) 0, MetricComplete (F.metric t) :=
    fun t ht => L.complete t (hsub ht)
  have hop : ∀ t ∈ Icc (-T) 0, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x :=
    fun t ht x => L.nonnegative_curvature_operator t (hsub ht) x
  obtain ⟨B, hB, hbound⟩ :=
    L.curvature_locally_bounded_in_time (Icc (-T) 0) isCompact_Icc hsub
  have hRic : (L.flow.connection 0).NonnegativeRicciCurvature := by
    intro x v
    exact ((L.flow.connection 0).ricci_bounds_of_nonnegative_curvatureOperator
      (P.m04.tensor_calculus 3 L.carrier.carrier (L.flow.metric 0) (L.flow.connection 0))
      x (L.nonnegative_curvature_operator 0 L.zero_mem x) v).1
  obtain ⟨hf, hu, _, hz, hfzero⟩ :=
    (L.flow.metric 0).busemann_parallel_unit_gradient (L.flow.connection 0)
      (L.complete 0 L.zero_mem) hRic hγ
  refine ⟨hf, hfzero, ?_⟩
  exact RicciFlow.Splitting.backward_persistence_of_parallel_gradient
    P.m04 (by norm_num) hneg F hc hop
    ⟨B, hB, fun t ht x => (le_abs_self _).trans (hbound t ht x)⟩ f hf hu hz

end PoincareConjecture.M32
