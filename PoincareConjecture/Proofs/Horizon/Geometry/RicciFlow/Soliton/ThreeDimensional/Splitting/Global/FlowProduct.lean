import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Flow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Components
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Completeness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.Ancient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.FactorFlow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.ParallelGradient.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Nonflatness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Classification












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow.Splitting

open RiemannianMetric



theorem exists_connectedComponent_ancient_product
    {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {r : M → ℝ} (hr : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r)
    (hunit : HasUnitGradient (F.connection 0) r)
    (hzero : HasZeroHessian (F.connection 0) r) (p : M) :
    let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
    let G := F.restrictComponent p
    ∃ (N : Type u) (_ : TopologicalSpace N) (_ : T3Space N)
      (_ : ConnectedSpace N) (_ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) N)
      (_ : IsManifold (𝓡 2) ∞ N) (H : RicciFlow 2 N (Iic 0)),
      (∀ t ≤ 0, MetricComplete (H.metric t)) ∧
      (∀ t ≤ 0, ∀ y, (H.connection t).NonnegativeCurvatureOperator y) ∧
      (∀ t ≤ 0, ∀ y, (H.connection t).curvatureTensorNorm y ≤ K) ∧
      (∀ t ≤ 0, ∀ q, 0 < (G.connection t).scalarCurvature q →
        ∃ y, 0 < (H.connection t).scalarCurvature y) ∧
      ∃ e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ C,
        (∀ t ≤ 0, ∀ (z : N × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
          (G.metric t).inner (e z)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
              (H.metric t).inner z.1 v.1 w.1 + v.2 * w.2) ∧
        (∀ q, (e.symm q).2 = r q.1) := by
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
  let G := F.restrictComponent p
  let rC : C → ℝ := r ∘ Subtype.val
  obtain ⟨hconn, _, hrs, hus, hzs⟩ :=
    connectedComponent_complete_parallel_coordinate (F.connection 0)
      hr hunit hzero (hcomplete 0 le_rfl) p
  let : ConnectedSpace C := hconn
  change HasUnitGradient (G.connection 0) rC at hus
  change HasZeroHessian (G.connection 0) rC at hzs
  have hcG (t : ℝ) (ht : t ≤ 0) : MetricComplete (G.metric t) :=
    F.restrictComponent_metricComplete p t (hcomplete t ht)
  have hopG (t : ℝ) (ht : t ≤ 0) (q : C) :
      (G.connection t).NonnegativeCurvatureOperator q :=
    (F.restrictComponent_nonnegativeCurvatureOperator_iff p t q).mpr (hoperator t ht q.1)
  have hboundG (t : ℝ) (ht : t ≤ 0) (q : C) :
      (G.connection t).curvatureTensorNorm q ≤ K := by
    rw [F.restrictComponent_curvatureTensorNorm p t q]
    exact hbound t ht q.1
  have hpersist := ancient_parallel_gradient hC (by norm_num : 1 ≤ 3) G hcG hopG
    ⟨K, hK, hboundG⟩ rC hrs hus hzs
  have huG := fun t ht => (hpersist t ht).2.1
  have hzG := fun t ht => (hpersist t ht).2.2
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun q (_ : q ∈ (⊤ : Opens C)) => regular_of_hasUnitGradient hus q
  let := openLevelSetChartedSpace hrs (⊤ : Opens C) hreg 2 0
  let := isManifold_openLevelSet hrs (⊤ : Opens C) hreg 2 0
  let H := G.parallelGradientFactor hrs (show (0 : ℝ) ∈ Iic 0 by simp) huG hzG
  obtain ⟨_, hconnN, hcN, hopN, hboundN, hposN⟩ :=
    G.parallelGradientFactor_geometry hrs (show (0 : ℝ) ∈ Iic 0 by simp)
      huG hzG hcG hopG hboundG
  obtain ⟨_, _, _, Φ, e, h0, hΦ, hs, he, _, _, hcoord, _⟩ :=
    exists_parallelGradient_productIsometry (hcG 0 le_rfl) hrs hus hzs
  refine ⟨zeroLevelSet rC, inferInstance, inferInstance, hconnN,
    inferInstance, inferInstance, H, hcN, hopN, hboundN, hposN, e, ?_, hcoord⟩
  intro t ht z v w
  have hΦt (q : C) : IsMIntegralCurve (fun s => Φ s q) ((G.connection t).gradient rC) := by
    rw [(hpersist t ht).1]
    exact hΦ q
  have heq : (e : zeroLevelSet rC × ℝ → C) =
      (fun z => Φ z.2 (zeroLevelIncl rC z.1)) := funext he
  rw [heq]
  exact gradientFlow_product_metric hrs (huG t ht) (hzG t ht) hs hΦt h0 z v w



theorem exists_unitRicciKernelFlow_component_ancient_product
    {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M (Iic 0))
    (hc : IsCoveringMap (unitRicciKernelProjection (F.connection 0)))
    (hcard : ∀ x, Nat.card (unitRicciKernelProjection (F.connection 0) ⁻¹' {x}) = 2)
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (r : UnitRicciKernel (F.connection 0) → ℝ)
    (p : UnitRicciKernel (F.connection 0)) :
    letI := unitRicciKernelChartedSpace (F.connection 0) hc
    letI := unitRicciKernelIsManifold (F.connection 0) hc
    letI := unitRicciKernelT3Space (F.connection 0) hc
    let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
    let G := (unitRicciKernelFlow F hc).restrictComponent p
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r →
    HasUnitGradient (unitRicciKernelMetric (F.connection 0) hc).leviCivitaData r →
    HasZeroHessian (unitRicciKernelMetric (F.connection 0) hc).leviCivitaData r →
    ∃ (N : Type u) (_ : TopologicalSpace N) (_ : T3Space N)
      (_ : ConnectedSpace N) (_ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) N)
      (_ : IsManifold (𝓡 2) ∞ N) (H : RicciFlow 2 N (Iic 0)),
      (∀ t ≤ 0, MetricComplete (H.metric t)) ∧
      (∀ t ≤ 0, ∀ y, (H.connection t).NonnegativeCurvatureOperator y) ∧
      (∀ t ≤ 0, ∀ y, (H.connection t).curvatureTensorNorm y ≤ K) ∧
      (∀ t ≤ 0, ∀ q, 0 < (G.connection t).scalarCurvature q →
        ∃ y, 0 < (H.connection t).scalarCurvature y) ∧
      ∃ e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ C,
        (∀ t ≤ 0, ∀ (z : N × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
          (G.metric t).inner (e z)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
              (H.metric t).inner z.1 v.1 w.1 + v.2 * w.2) ∧
        (∀ q, (e.symm q).2 = r q.1) := by
  let := unitRicciKernelChartedSpace (F.connection 0) hc
  let := unitRicciKernelIsManifold (F.connection 0) hc
  let : T2Space (UnitRicciKernel (F.connection 0)) :=
    unitRicciKernelT2Space_of_covering hc
  let := unitRicciKernelT3Space (F.connection 0) hc
  intro C G hr hu hz
  apply exists_connectedComponent_ancient_product hC (unitRicciKernelFlow F hc)
    (fun t ht => unitRicciKernelFlow_metricComplete F hc hcard t (hcomplete t ht))
    (fun t ht q => (unitRicciKernelFlow_nonnegativeCurvatureOperator_iff F hc t q).mpr
      (hoperator t ht _)) hK ?_ hr hu hz p
  intro t ht q
  rw [unitRicciKernelFlow_curvatureTensorNorm]
  exact hbound t ht _




theorem exists_ancientRound_product_of_parallel_coordinate
    {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (F : RicciFlow 3 M (Iic 0))
    (hc : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hop : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ) (hnc : AncientKappaNoncollapsed F κ)
    (hscalar : ∃ x, 0 < (F.connection 0).scalarCurvature x)
    {r : M → ℝ} (hr : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r)
    (hunit : HasUnitGradient (F.connection 0) r)
    (hzero : HasZeroHessian (F.connection 0) r) :
    ∃ (N : Type u) (_ : TopologicalSpace N) (_ : T3Space N)
      (_ : ConnectedSpace N) (_ : MeasurableSpace N) (_ : BorelSpace N)
      (_ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) N)
      (_ : IsManifold (𝓡 2) ∞ N) (_ : SecondCountableTopology N)
      (A : AncientKappaSolution 2 N),
      A.kappa = κ / 2 ∧ Nonempty (TwoDimensionalAncientRoundCertificate A) ∧
      ∃ e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M,
        (∀ t ≤ 0, ∀ (z : N × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
          (F.metric t).inner (e z)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
              (A.flow.metric t).inner z.1 v.1 w.1 + v.2 * w.2) ∧
        (∀ q, (e.symm q).2 = r q) := by
  let : SecondCountableTopology M := (F.metric 0).secondCountableTopology
  have hp := ancient_parallel_gradient hP.curvature (by norm_num : 1 ≤ 3) F
    hc hop ⟨K, hK, hbound⟩ r hr hunit hzero
  let huall := fun t ht => (hp t ht).2.1
  let hzall := fun t ht => (hp t ht).2.2
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun q (_ : q ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hunit q
  let := openLevelSetChartedSpace hr (⊤ : Opens M) hreg 2 0
  let := isManifold_openLevelSet hr (⊤ : Opens M) hreg 2 0
  let H := F.parallelGradientFactor hr (show (0 : ℝ) ∈ Iic 0 by simp) huall hzall
  obtain ⟨hne, hconn, hcN, hopN, hboundN, hposN⟩ :=
    F.parallelGradientFactor_geometry hr (show (0 : ℝ) ∈ Iic 0 by simp)
      huall hzall hc hop hbound
  let : ConnectedSpace (zeroLevelSet r) := hconn
  let : Nonempty (zeroLevelSet r) := hne
  let : SecondCountableTopology (zeroLevelSet r) := (H.metric 0).secondCountableTopology
  obtain ⟨_, _, _, Φ, e, h0, hΦ, hs, he, _, _, hcoord, _⟩ :=
    exists_parallelGradient_productIsometry (hc 0 le_rfl) hr hunit hzero
  let : NoncompactSpace M := e.toHomeomorph.isClosedEmbedding.noncompactSpace
  have hpast := F.scalarCurvature_positive_somewhere_of_bounded_ancient
    hP.curvature hc hop hK hbound hscalar
  have hnonflat : ∀ t ≤ 0, ∃ y, (H.connection t).curvatureTensorNorm y ≠ 0 := by
    intro t ht
    obtain ⟨x, hx⟩ := hpast t ht
    obtain ⟨y, hy⟩ := hposN t ht x hx
    refine ⟨y, fun hz => ?_⟩
    have hb := (H.connection t).abs_scalarCurvature_le_curvatureTensorNorm y
    rw [hz, mul_zero] at hb
    exact hy.not_ge ((le_abs_self _).trans hb)
  let A : AncientKappaSolution 2 (zeroLevelSet r) :=
    { flow := H
      kappa := κ / 2
      kappa_pos := by positivity
      complete := hcN
      nonnegative_curvature_operator := hopN
      bounded_curvature := fun t ht => ⟨K, hK, fun y => by
        rw [abs_of_nonneg (show 0 ≤ (H.connection t).curvatureTensorNorm y from
          Real.sqrt_nonneg _)]
        exact hboundN t ht y⟩
      nonflat := hnonflat
      noncollapsed := F.parallelGradientFactor_parabolic_noncollapsed hc hr
        huall hzall (fun t ht => (hp t ht).1) hnc }
  refine ⟨zeroLevelSet r, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    A, rfl, hP.two_dimensional.ancient_classification A, e, ?_, hcoord⟩
  intro t ht z v w
  have hΦt (q : M) : IsMIntegralCurve (fun s => Φ s q) ((F.connection t).gradient r) := by
    rw [(hp t ht).1]
    exact hΦ q
  have heq : (e : zeroLevelSet r × ℝ → M) =
      (fun z => Φ z.2 (zeroLevelIncl r z.1)) := funext he
  rw [heq]
  exact gradientFlow_product_metric hr (huall t ht) (hzall t ht) hs hΦt h0 z v w

end PoincareConjecture.RicciFlow.Splitting
