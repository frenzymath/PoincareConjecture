import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.ParallelGradient.AncientFactor
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Classification
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.AncientRescaledLimit







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u
namespace PoincareConjecture.RicciFlow

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology
attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

theorem exists_compact_round_surface_product_of_minimizing_line
    {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (P : ThreeDimensionalClassificationPredecessors.{u})
    (F : RicciFlow 3 M (Iic 0))
    (hc : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hop : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ B)
    {κ : ℝ} (hκ : 0 < κ) (hnc : AncientKappaNoncollapsed F κ)
    (hscalar : ∃ p, 0 < (F.connection 0).scalarCurvature p)
    (γ : ℝ → M)
    (hγ : ∀ s t : ℝ, (F.metric 0).edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    ∃ C : FlowCarrier.{u} 2,
      letI : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
      ∃ A : AncientKappaSolution 2 C.carrier,
        A.kappa = κ / 2 ∧ Nonempty (TwoDimensionalAncientRoundCertificate A) ∧
        ∃ e : (C.carrier × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M,
          (∀ t ≤ 0, ∀ (z : C.carrier × ℝ)
            (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
            (F.metric t).inner (e z)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
                (A.flow.metric t).inner z.1 v.1 w.1 + v.2 * w.2) ∧
          (∀ t ≤ 0, ∀ x,
            (A.flow.connection t).curvatureTensorNorm (e.symm x).1 =
              (F.connection t).curvatureTensorNorm x)

 := by
  let : SecondCountableTopology M := (F.metric 0).secondCountableTopology
  let f := (F.metric 0).busemann γ
  obtain ⟨hf, hu, hz, hconn, A, hflow, hconstant, e, _, hmetric, hnorm⟩ :=
    F.exists_ancientKappaSolution_factor_of_minimizing_line
      P.curvature hc hop hB hbound hκ hnc hscalar γ hγ
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := Poincare.Geometry.Manifold.RegularLevel.openLevelSetChartedSpace hf
    (⊤ : TopologicalSpace.Opens M)
    (fun x _ => RiemannianMetric.regular_of_hasUnitGradient hu x) 2 0
  let := Poincare.Geometry.Manifold.RegularLevel.isManifold_openLevelSet hf
    (⊤ : TopologicalSpace.Opens M)
    (fun x _ => RiemannianMetric.regular_of_hasUnitGradient hu x) 2 0
  let : ConnectedSpace (RiemannianMetric.zeroLevelSet f) := hconn
  let C := FlowCarrier.ofConnectedManifold 2
    (RiemannianMetric.zeroLevelSet f)
  refine ⟨C, A, hconstant, P.two_dimensional.ancient_classification A, e, hmetric, hnorm⟩

end PoincareConjecture.RicciFlow
