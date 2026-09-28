import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Source
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.FlowProduct
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.ComponentCover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.SolitonEquation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow.Splitting

open RiemannianMetric

variable {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
  [ConnectedSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]



def CanonicalAncientRoundProduct (F : RicciFlow 3 M (Iic 0)) {r : M → ℝ}
    (hr : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r)
    (hu : HasUnitGradient (F.connection 0) r) (φ : M → ℝ) (κ : ℝ) : Prop :=
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
    ⟨finrank_euclideanSpace_fin⟩
  letI := openLevelSetChartedSpace hr (⊤ : Opens M)
    (fun x _ => regular_of_hasUnitGradient hu x) 2 0
  letI := isManifold_openLevelSet hr (⊤ : Opens M)
    (fun x _ => regular_of_hasUnitGradient hu x) 2 0
  ∃ hconn : ConnectedSpace (zeroLevelSet r),
    letI := hconn
    ∃ A : AncientKappaSolution 2 (zeroLevelSet r),
      A.kappa = κ / 2 ∧
      A.flow.metric 0 = regularLevelMetric hr (⊤ : Opens M)
        (fun x _ => regular_of_hasUnitGradient hu x) 0 (F.metric 0) ∧
      Nonempty (TwoDimensionalAncientRoundCertificate A) ∧
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 (φ ∘ zeroLevelIncl r) ∧
      (∀ (y : zeroLevelSet r) (a b : TangentSpace (𝓡 2) y),
        (A.flow.connection 0).ricci y a b +
          (A.flow.connection 0).hessian (φ ∘ zeroLevelIncl r) y a b =
            (1 / 2 : ℝ) * (A.flow.metric 0).inner y a b) ∧
      ∃ e : (zeroLevelSet r × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M,
        (∀ t ≤ 0, ∀ (z : zeroLevelSet r × ℝ)
          (a b : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
          (F.metric t).inner (e z)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z a)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z b) =
              (A.flow.metric t).inner z.1 a.1 b.1 + a.2 * b.2) ∧
        (∀ q, (e.symm q).2 = r q)



theorem canonicalAncientRoundProduct_of_parallel_coordinate
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (F : RicciFlow 3 M (Iic 0))
    (hc : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hop : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ) (hnc : AncientKappaNoncollapsed F κ)
    (hscalar : ∃ x, 0 < (F.connection 0).scalarCurvature x)
    {r φ : M → ℝ} (hr : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r)
    (hu : HasUnitGradient (F.connection 0) r)
    (hz : HasZeroHessian (F.connection 0) r)
    (hφ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) 2 φ)
    (hsol : ∀ (x : M) (a b : TangentSpace (𝓡 3) x),
      (F.connection 0).ricci x a b + (F.connection 0).hessian φ x a b =
        (1 / 2 : ℝ) * (F.metric 0).inner x a b) :
    CanonicalAncientRoundProduct F hr hu φ κ := by
  have hp := ancient_parallel_gradient hP.curvature (by norm_num : 1 ≤ 3) F
    hc hop ⟨K, hK, hbound⟩ r hr hu hz
  let huall := fun t ht => (hp t ht).2.1
  let hzall := fun t ht => (hp t ht).2.2
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun q (_ : q ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hu q
  let := openLevelSetChartedSpace hr (⊤ : Opens M) hreg 2 0
  let := isManifold_openLevelSet hr (⊤ : Opens M) hreg 2 0
  let H := F.parallelGradientFactor hr (show (0 : ℝ) ∈ Iic 0 by simp) huall hzall
  obtain ⟨hne, hconn, hcN, hopN, hboundN, hposN⟩ :=
    F.parallelGradientFactor_geometry hr (show (0 : ℝ) ∈ Iic 0 by simp)
      huall hzall hc hop hbound
  let : ConnectedSpace (zeroLevelSet r) := hconn
  let : Nonempty (zeroLevelSet r) := hne
  obtain ⟨_, _, _, Φ, e, h0, hΦ, hs, he, _, _, hcoord, _⟩ :=
    exists_parallelGradient_productIsometry (hc 0 le_rfl) hr hu hz
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
  refine ⟨hconn, A, rfl, rfl, hP.two_dimensional.ancient_classification A, ?_, ?_,
    e, ?_, hcoord⟩
  · exact hφ.comp ((contMDiff_openLevelIncl hr (⊤ : Opens M) hreg 2 0).of_le
      (by norm_cast : (2 : ℕ∞ω) ≤ ∞))
  · exact parallelGradient_factor_soliton_equation hr hu hz hφ hsol
  · intro t ht z a b
    have hΦt (q : M) : IsMIntegralCurve (fun s => Φ s q) ((F.connection t).gradient r) := by
      rw [(hp t ht).1]
      exact hΦ q
    have heq : (e : zeroLevelSet r × ℝ → M) =
        (fun z => Φ z.2 (zeroLevelIncl r z.1)) := funext he
    rw [heq]
    exact gradientFlow_product_metric hr (huall t ht) (hzall t ht) hs hΦt h0 z a b

end PoincareConjecture.RicciFlow.Splitting

namespace PoincareConjecture.ShrinkingSolitonFlow

open RicciFlow.Splitting RiemannianMetric

variable {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
  [ConnectedSpace M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S)




theorem exists_nullCover_component_ancientRound_product
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : S.metric.inner x v v = 1) (hw : S.metric.inner x w w = 1)
    (hvw : S.metric.inner x v w = 0)
    (hzero : S.connection.curvatureTensor x v w v w = 0) :
    ∃ hc : IsCoveringMap (unitRicciKernelProjection (G.ancientSourceFlow.connection 0)),
      (∀ y : M, Nat.card (unitRicciKernelProjection
        (G.ancientSourceFlow.connection 0) ⁻¹' {y}) = 2) ∧
      letI := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
      letI := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
      letI := unitRicciKernelT3Space (G.ancientSourceFlow.connection 0) hc
      ∀ p : UnitRicciKernel (G.ancientSourceFlow.connection 0),
      let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
      let F := (unitRicciKernelFlow G.ancientSourceFlow hc).restrictComponent p
      Function.Surjective (fun q : C => unitRicciKernelProjection
        (G.ancientSourceFlow.connection 0) q.1) ∧
      ∃ (N : Type u) (_ : TopologicalSpace N) (_ : T3Space N)
        (_ : ConnectedSpace N) (_ : MeasurableSpace N) (_ : BorelSpace N)
        (_ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) N)
        (_ : IsManifold (𝓡 2) ∞ N) (_ : SecondCountableTopology N)
        (A : AncientKappaSolution 2 N),
        A.kappa = S.kappa / 2 ∧ Nonempty (TwoDimensionalAncientRoundCertificate A) ∧
        ∃ e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ C,
          (∀ t ≤ 0, ∀ (z : N × ℝ) (a b : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
            (F.metric t).inner (e z)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z a)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z b) =
                (A.flow.metric t).inner z.1 a.1 b.1 + a.2 * b.2) ∧
          (∀ q, (e.symm q).2 = unitRicciKernelCoordinate
            (G.ancientSourceFlow.connection 0) S.potential q.1) := by
  obtain ⟨hc, hcard, hgeom⟩ :=
    G.exists_complete_nullCover_coordinate hP.curvature x v w hv hw hvw hzero
  refine ⟨hc, hcard, ?_⟩
  let := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
  let := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
  let : T2Space (UnitRicciKernel (G.ancientSourceFlow.connection 0)) :=
    unitRicciKernelT2Space_of_covering hc
  let := unitRicciKernelT3Space (G.ancientSourceFlow.connection 0) hc
  let : MeasurableSpace (UnitRicciKernel (G.ancientSourceFlow.connection 0)) :=
    borel (UnitRicciKernel (G.ancientSourceFlow.connection 0))
  let : BorelSpace (UnitRicciKernel (G.ancientSourceFlow.connection 0)) := ⟨rfl⟩
  let L := unitRicciKernelFlow G.ancientSourceFlow hc
  let r := unitRicciKernelCoordinate (G.ancientSourceFlow.connection 0) S.potential
  obtain ⟨hc0, hr, hu, hz, _⟩ := hgeom
  intro p C F
  have hsurj := unitRicciKernelComponent_projection_surjective
    (G.ancientSourceFlow.connection 0) hc hcard p
  refine ⟨hsurj, ?_⟩
  obtain ⟨hconn, _, hrC, huC, hzC⟩ :=
    connectedComponent_complete_parallel_coordinate (L.connection 0) hr hu hz hc0 p
  let : ConnectedSpace C := hconn
  change HasUnitGradient (F.connection 0) (r ∘ Subtype.val) at huC
  change HasZeroHessian (F.connection 0) (r ∘ Subtype.val) at hzC
  have hcomplete (t : ℝ) (ht : t ≤ 0) : MetricComplete (F.metric t) :=
    L.restrictComponent_metricComplete p t
      (unitRicciKernelFlow_metricComplete G.ancientSourceFlow hc hcard t
        (G.ancientSource.complete t ht))
  have hop (t : ℝ) (ht : t ≤ 0) (q : C) :
      (F.connection t).NonnegativeCurvatureOperator q :=
    (L.restrictComponent_nonnegativeCurvatureOperator_iff p t q).mpr
      ((unitRicciKernelFlow_nonnegativeCurvatureOperator_iff G.ancientSourceFlow hc t q.1).mpr
        (G.ancientSource.nonnegative_curvature_operator t ht _))
  obtain ⟨K, hK, hbound⟩ := G.ancientSourceFlow_uniformCurvatureBound
  have hnorm (t : ℝ) (ht : t ≤ 0) (q : C) :
      (F.connection t).curvatureTensorNorm q ≤ K := by
    rw [L.restrictComponent_curvatureTensorNorm p t q,
      unitRicciKernelFlow_curvatureTensorNorm]
    exact (le_abs_self _).trans (hbound t ht _)
  have hncL (t : ℝ) (ht : t ≤ 0) :
      MetricKappaNoncollapsed (L.metric t) (L.connection t) S.kappa :=
    MetricKappaNoncollapsed.of_covering (L.connection t) (G.ancientSourceFlow.connection t)
      (unitRicciKernelProjection_isLocalDiffeomorph (G.ancientSourceFlow.connection 0) hc)
      hc (fun _ _ _ => rfl) (G.ancientSourceFlow_metricKappaNoncollapsed t ht)
  have hncC (t : ℝ) (ht : t ≤ 0) :
      MetricKappaNoncollapsed (F.metric t) (F.connection t) S.kappa :=
    MetricKappaNoncollapsed.connectedComponentMetric (L.connection t) (hncL t ht) p
  have hanc : AncientKappaNoncollapsed F S.kappa := by
    intro r₀ hr₀ t ht q r₀' hr hrr hcurv
    exact (hncC t ht).2 q r₀' hr
      (hcurv t ⟨by nlinarith [sq_pos_of_pos hr], le_rfl⟩)
  have hscalar : ∃ q, 0 < (F.connection 0).scalarCurvature q := by
    obtain ⟨y, hy⟩ := G.ancientSource.nonflat 0 le_rfl
    obtain ⟨q, hq⟩ := hsurj y
    change unitRicciKernelProjection (G.ancientSourceFlow.connection 0) q.1 = y at hq
    refine ⟨q, ?_⟩
    rw [L.restrictComponent_scalarCurvature p 0 q,
      unitRicciKernelFlow_scalarCurvature, hq]
    exact (lt_of_le_of_ne (Real.sqrt_nonneg _) hy.symm).trans_le
      ((G.ancientSourceFlow.connection 0).curvatureTensorNorm_le_scalarCurvature_sharp
        (hP.curvature.tensor_calculus 3 M _ _) y
        (G.ancientSource.nonnegative_curvature_operator 0 le_rfl y))
  exact exists_ancientRound_product_of_parallel_coordinate hP F hcomplete hop hK hnorm
    S.kappa_pos hanc hscalar hrC huC hzC



theorem exists_nullCover_component_canonicalAncientRound_product
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : S.metric.inner x v v = 1) (hw : S.metric.inner x w w = 1)
    (hvw : S.metric.inner x v w = 0)
    (hzero : S.connection.curvatureTensor x v w v w = 0) :
    ∃ hc : IsCoveringMap (unitRicciKernelProjection (G.ancientSourceFlow.connection 0)),
      (∀ y : M, Nat.card (unitRicciKernelProjection
        (G.ancientSourceFlow.connection 0) ⁻¹' {y}) = 2) ∧
      letI := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
      letI := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
      letI := unitRicciKernelT2Space_of_covering hc
      letI := unitRicciKernelT3Space (G.ancientSourceFlow.connection 0) hc
      letI : MeasurableSpace (UnitRicciKernel (G.ancientSourceFlow.connection 0)) :=
        borel (UnitRicciKernel (G.ancientSourceFlow.connection 0))
      letI : BorelSpace (UnitRicciKernel (G.ancientSourceFlow.connection 0)) := ⟨rfl⟩
      ∀ p : UnitRicciKernel (G.ancientSourceFlow.connection 0),
      let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
      let F := (unitRicciKernelFlow G.ancientSourceFlow hc).restrictComponent p
      letI : SecondCountableTopology C := (F.metric 0).secondCountableTopology
      let r : C → ℝ := unitRicciKernelCoordinate
        (G.ancientSourceFlow.connection 0) S.potential ∘ Subtype.val
      let projection : C → M := fun q => unitRicciKernelProjection
        (G.ancientSourceFlow.connection 0) q.1
      Function.Surjective projection ∧
      ∃ hr : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r,
      ∃ hu : HasUnitGradient (F.connection 0) r,
        CanonicalAncientRoundProduct F hr hu (S.potential ∘ projection) S.kappa := by
  obtain ⟨hc, hcard, hgeom⟩ :=
    G.exists_complete_nullCover_coordinate hP.curvature x v w hv hw hvw hzero
  refine ⟨hc, hcard, ?_⟩
  let := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
  let := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
  let : T2Space (UnitRicciKernel (G.ancientSourceFlow.connection 0)) :=
    unitRicciKernelT2Space_of_covering hc
  let := unitRicciKernelT3Space (G.ancientSourceFlow.connection 0) hc
  let : MeasurableSpace (UnitRicciKernel (G.ancientSourceFlow.connection 0)) :=
    borel (UnitRicciKernel (G.ancientSourceFlow.connection 0))
  let : BorelSpace (UnitRicciKernel (G.ancientSourceFlow.connection 0)) := ⟨rfl⟩
  let L := unitRicciKernelFlow G.ancientSourceFlow hc
  let r := unitRicciKernelCoordinate (G.ancientSourceFlow.connection 0) S.potential
  obtain ⟨hc0, hr, hu, hz, _⟩ := hgeom
  intro p
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
  let F := (unitRicciKernelFlow G.ancientSourceFlow hc).restrictComponent p
  let hsecond : SecondCountableTopology C := (F.metric 0).secondCountableTopology
  let rC : C → ℝ := unitRicciKernelCoordinate
    (G.ancientSourceFlow.connection 0) S.potential ∘ Subtype.val
  let projection : C → M := fun q => unitRicciKernelProjection
    (G.ancientSourceFlow.connection 0) q.1
  let : SecondCountableTopology C := hsecond
  have hsurj := unitRicciKernelComponent_projection_surjective
    (G.ancientSourceFlow.connection 0) hc hcard p
  obtain ⟨_, _, hrC, huC, hzC⟩ :=
    connectedComponent_complete_parallel_coordinate (L.connection 0) hr hu hz hc0 p
  change HasUnitGradient (F.connection 0) rC at huC
  change HasZeroHessian (F.connection 0) rC at hzC
  refine ⟨hsurj, hrC, huC, ?_⟩
  have hcomplete (t : ℝ) (ht : t ≤ 0) : MetricComplete (F.metric t) :=
    L.restrictComponent_metricComplete p t
      (unitRicciKernelFlow_metricComplete G.ancientSourceFlow hc hcard t
        (G.ancientSource.complete t ht))
  have hop (t : ℝ) (ht : t ≤ 0) (q : C) :
      (F.connection t).NonnegativeCurvatureOperator q :=
    (L.restrictComponent_nonnegativeCurvatureOperator_iff p t q).mpr
      ((unitRicciKernelFlow_nonnegativeCurvatureOperator_iff G.ancientSourceFlow hc t q.1).mpr
        (G.ancientSource.nonnegative_curvature_operator t ht _))
  obtain ⟨K, hK, hbound⟩ := G.ancientSourceFlow_uniformCurvatureBound
  have hnorm (t : ℝ) (ht : t ≤ 0) (q : C) :
      (F.connection t).curvatureTensorNorm q ≤ K := by
    rw [L.restrictComponent_curvatureTensorNorm p t q,
      unitRicciKernelFlow_curvatureTensorNorm]
    exact (le_abs_self _).trans (hbound t ht _)
  have hncL (t : ℝ) (ht : t ≤ 0) :
      MetricKappaNoncollapsed (L.metric t) (L.connection t) S.kappa :=
    MetricKappaNoncollapsed.of_covering (L.connection t) (G.ancientSourceFlow.connection t)
      (unitRicciKernelProjection_isLocalDiffeomorph (G.ancientSourceFlow.connection 0) hc)
      hc (fun _ _ _ => rfl) (G.ancientSourceFlow_metricKappaNoncollapsed t ht)
  have hncC (t : ℝ) (ht : t ≤ 0) :
      MetricKappaNoncollapsed (F.metric t) (F.connection t) S.kappa :=
    MetricKappaNoncollapsed.connectedComponentMetric (L.connection t) (hncL t ht) p
  have hanc : AncientKappaNoncollapsed F S.kappa := by
    intro r₀ hr₀ t ht q r₀' hr hrr hcurv
    exact (hncC t ht).2 q r₀' hr
      (hcurv t ⟨by nlinarith [sq_pos_of_pos hr], le_rfl⟩)
  have hscalar : ∃ q, 0 < (F.connection 0).scalarCurvature q := by
    obtain ⟨y, hy⟩ := G.ancientSource.nonflat 0 le_rfl
    obtain ⟨q, hq⟩ := hsurj y
    change unitRicciKernelProjection (G.ancientSourceFlow.connection 0) q.1 = y at hq
    refine ⟨q, ?_⟩
    rw [L.restrictComponent_scalarCurvature p 0 q,
      unitRicciKernelFlow_scalarCurvature, hq]
    exact (lt_of_le_of_ne (Real.sqrt_nonneg _) hy.symm).trans_le
      ((G.ancientSourceFlow.connection 0).curvatureTensorNorm_le_scalarCurvature_sharp
        (hP.curvature.tensor_calculus 3 M _ _) y
        (G.ancientSource.nonnegative_curvature_operator 0 le_rfl y))
  have hπ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ projection :=
    unitRicciKernelComponent_projection_isLocalDiffeomorph
      (G.ancientSourceFlow.connection 0) hc p
  have hmetric (q : C) (a b : TangentSpace (𝓡 3) q) :
      (F.metric 0).inner q a b = (G.ancientSourceFlow.metric 0).inner (projection q)
        (mfderiv (𝓡 3) (𝓡 3) projection q a) (mfderiv (𝓡 3) (𝓡 3) projection q b) := by
    change _ = (G.ancientSourceFlow.metric 0).inner (projection q)
      (mfderiv (𝓡 3) (𝓡 3)
        (unitRicciKernelProjection (G.ancientSourceFlow.connection 0) ∘ Subtype.val) q a)
      (mfderiv (𝓡 3) (𝓡 3)
        (unitRicciKernelProjection (G.ancientSourceFlow.connection 0) ∘ Subtype.val) q b)
    rw [mfderiv_comp q
      ((unitRicciKernelProjection_isLocalDiffeomorph
        (G.ancientSourceFlow.connection 0) hc).mdifferentiable (by simp) q.1)
      ((Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) C).mdifferentiable (by simp) q)]
    rfl
  have hφ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) 2 (S.potential ∘ projection) :=
    S.potential_C2.comp (hπ.contMDiff.of_le (by norm_cast : (2 : ℕ∞ω) ≤ ∞))
  have hsol (q : C) (a b : TangentSpace (𝓡 3) q) :
      (F.connection 0).ricci q a b +
        (F.connection 0).hessian (S.potential ∘ projection) q a b =
          (1 / 2 : ℝ) * (F.metric 0).inner q a b := by
    rw [(F.connection 0).ricci_eq_of_local_isometry (G.ancientSourceFlow.connection 0)
      isOpen_univ hπ.contMDiff.contMDiffOn (fun q _ => hmetric q) (mem_univ q),
      (F.connection 0).hessian_comp_of_metric_pullback_of_C2
        (G.ancientSourceFlow.connection 0) (hπ.contMDiff q)
        (Eventually.of_forall fun y => ⟨hπ.mfderivToContinuousLinearEquiv (by simp) y, rfl⟩)
        (Eventually.of_forall hmetric) (S.potential_C2 (projection q)), hmetric]
    exact G.ancientSourceFlow_soliton_equation (projection q) _ _
  exact canonicalAncientRoundProduct_of_parallel_coordinate hP F hcomplete hop hK hnorm
    S.kappa_pos hanc hscalar hrC huC hzC hφ hsol

end PoincareConjecture.ShrinkingSolitonFlow
