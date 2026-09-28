import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Graphs.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.Factor
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.AtInfinity.Normalized

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.ShrinkingSolitonFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S) {q : ℕ → M}
  (L : AncientPointedGeometricConvergence
    (fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (fun _ => G.unscaledSourceFlow.shrink.metric)
    (fun k => equivShrink M (q k)) 1)
  (B : G.NormalizedPotentialLimit L)

theorem exists_zeroLevel_potentialLevelGraphs
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (hD : S.connection.CurvatureTensorCalculus) (p : M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (hcomplete : MetricComplete (L.limitFlow.metric 0)) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace B.potential_contMDiff (⊤ : Opens L.limitCarrier.carrier)
      (fun x _ => RiemannianMetric.regular_of_hasUnitGradient B.unitGradient x) 2 0
    letI := isManifold_openLevelSet B.potential_contMDiff (⊤ : Opens L.limitCarrier.carrier)
      (fun x _ => RiemannianMetric.regular_of_hasUnitGradient B.unitGradient x) 2 0
    let h := RiemannianMetric.regularLevelMetric B.potential_contMDiff
      (⊤ : Opens L.limitCarrier.carrier)
      (fun x _ => RiemannianMetric.regular_of_hasUnitGradient B.unitGradient x) 0
      (L.limitFlow.metric 0)
    let base : RiemannianMetric.zeroLevelSet B.potential :=
      ⟨⟨L.base, mem_univ _⟩, B.potential_base⟩
    ConnectedSpace (RiemannianMetric.zeroLevelSet B.potential) ∧
      CompactSpace (RiemannianMetric.zeroLevelSet B.potential) ∧ MetricComplete h ∧
      (∀ y, h.leviCivitaData.scalarCurvature y = 1) ∧
      ∃ e : (RiemannianMetric.zeroLevelSet B.potential × ℝ)
          ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ L.limitCarrier.carrier,
        (∀ z, B.potential (e z) = z.2) ∧
        (∀ (z : RiemannianMetric.zeroLevelSet B.potential × ℝ)
          (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
          (L.limitFlow.metric 0).inner (e z)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
            h.inner z.1 v.1 w.1 + v.2 * w.2) ∧
        e (base, 0) = L.base ∧ Nonempty (G.PotentialLevelGraphs L B h e base) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens L.limitCarrier.carrier)) =>
    RiemannianMetric.regular_of_hasUnitGradient B.unitGradient x
  let := openLevelSetChartedSpace B.potential_contMDiff
    (⊤ : Opens L.limitCarrier.carrier) hreg 2 0
  let := isManifold_openLevelSet B.potential_contMDiff
    (⊤ : Opens L.limitCarrier.carrier) hreg 2 0
  let : ConnectedSpace L.limitCarrier.carrier :=
    connectedSpace_iff_univ.mpr L.limitCarrier.connected
  let h := RiemannianMetric.regularLevelMetric B.potential_contMDiff
    (⊤ : Opens L.limitCarrier.carrier) hreg 0 (L.limitFlow.metric 0)
  let base : RiemannianMetric.zeroLevelSet B.potential :=
    ⟨⟨L.base, mem_univ _⟩, B.potential_base⟩
  have hR (x : L.limitCarrier.carrier) : (L.limitFlow.connection 0).scalarCurvature x = 1 := by
    simpa only [sub_zero, div_one] using
      G.unscaledPointedLimit_scalarCurvature_eq_one_div_one_sub L hP p hescape hcomplete
        0 (by norm_num) x
  obtain ⟨_, hconn, hcompact, hc, hscalar⟩ :=
    RiemannianMetric.compact_unitScalar_zeroLevel_of_parallel hcomplete
      B.potential_contMDiff B.unitGradient B.zeroHessian hR
  let : CompactSpace (RiemannianMetric.zeroLevelSet B.potential) := hcompact
  obtain ⟨_, _, _, Φ, e, hzero, _, _, he, hpotential, hproduct, _, _⟩ :=
    RiemannianMetric.exists_parallelGradient_productIsometry hcomplete
      B.potential_contMDiff B.unitGradient B.zeroHessian
  have hebase : e (base, 0) = L.base := by
    rw [he, hzero]
    rfl
  exact ⟨hconn, hcompact, hc, hscalar, e, hpotential, hproduct, hebase,
    G.exists_potentialLevelGraphs L B hD p hescape h e hpotential hproduct base hebase⟩

end PoincareConjecture.ShrinkingSolitonFlow
