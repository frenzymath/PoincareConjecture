import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.CoverCoordinate
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Completeness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Product
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.PotentialRegularity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow.Splitting

theorem exists_complete_nullCover_coordinate
    {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M (Iic 0))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hnonflat : ∃ p, (F.connection 0).curvatureTensorNorm p ≠ 0)
    (hcomplete : MetricComplete (F.metric 0))
    (f : M → ℝ) (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ y, ∀ v w, (F.connection 0).ricci y v w +
      (F.connection 0).hessian f y v w = (1 / 2 : ℝ) * (F.metric 0).inner y v w)
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (F.metric 0).inner x v v = 1)
    (hw : (F.metric 0).inner x w w = 1)
    (hvw : (F.metric 0).inner x v w = 0)
    (hzero : (F.connection 0).curvatureTensor x v w v w = 0) :
    ∃ hc : IsCoveringMap (unitRicciKernelProjection (F.connection 0)),
      (∀ y : M, Nat.card (unitRicciKernelProjection (F.connection 0) ⁻¹' {y}) = 2) ∧
      letI := unitRicciKernelChartedSpace (F.connection 0) hc
      letI := unitRicciKernelIsManifold (F.connection 0) hc
      letI := unitRicciKernelT3Space (F.connection 0) hc
      let g' := unitRicciKernelMetric (F.connection 0) hc
      let r := unitRicciKernelCoordinate (F.connection 0) f
      MetricComplete g' ∧ ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r ∧
        RiemannianMetric.HasUnitGradient g'.leviCivitaData r ∧
        RiemannianMetric.HasZeroHessian g'.leviCivitaData r ∧
        ∀ p, r (unitRicciKernelReverse (F.connection 0) p) = -r p := by
  have hdim := F.ricciNullity_eq_one_of_terminal_null_plane hC hoperator hnonflat
    x v w hv hw hvw hzero
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
    (show Icc (-1 : ℝ) 0 ⊆ Iic (0 : ℝ) from fun _ hs => hs.2) ordConnected_Icc
    ⟨-1, by norm_num, 0, by norm_num, by norm_num⟩
  have hsec : ∀ s ∈ Icc (-1 : ℝ) 0, (G.connection s).NonnegativeSectionalCurvature := by
    intro s hs q a b
    exact (F.connection s).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      q (hoperator s hs.2 q) a b
  have hsmooth := (F.connection 0).contMDiff_of_C2_gradient_soliton hf hsol
  let hc := unitRicciKernel_isCoveringMap_of_terminal_nullity_one hC
    (by norm_num : (-1 : ℝ) < 0) G hsec hdim
  have hcard := unitRicciKernel_fiber_card_of_terminal_nullity_one hC
    (by norm_num : (-1 : ℝ) < 0) G hsec hdim
  refine ⟨hc, hcard, ?_⟩
  let := unitRicciKernelChartedSpace (F.connection 0) hc
  let := unitRicciKernelIsManifold (F.connection 0) hc
  let := unitRicciKernelT3Space (F.connection 0) hc
  obtain ⟨hr, hu, hz⟩ := unitRicciKernelCoordinate_geometry_of_terminal_soliton hC
    (by norm_num : (-1 : ℝ) < 0) G hsec hdim f hsmooth hsol
  exact ⟨unitRicciKernelMetric_complete (F.connection 0) hc hcard hcomplete,
    hr, hu, hz, unitRicciKernelCoordinate_reverse (F.connection 0) f⟩

theorem exists_nullCover_component_product
    {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M (Iic 0))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hnonflat : ∃ p, (F.connection 0).curvatureTensorNorm p ≠ 0)
    (hcomplete : MetricComplete (F.metric 0))
    (f : M → ℝ) (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ y, ∀ v w, (F.connection 0).ricci y v w +
      (F.connection 0).hessian f y v w = (1 / 2 : ℝ) * (F.metric 0).inner y v w)
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (F.metric 0).inner x v v = 1)
    (hw : (F.metric 0).inner x w w = 1)
    (hvw : (F.metric 0).inner x v w = 0)
    (hzero : (F.connection 0).curvatureTensor x v w v w = 0) :
    ∃ hc : IsCoveringMap (unitRicciKernelProjection (F.connection 0)),
      (∀ y : M, Nat.card (unitRicciKernelProjection (F.connection 0) ⁻¹' {y}) = 2) ∧
      letI := unitRicciKernelChartedSpace (F.connection 0) hc
      letI := unitRicciKernelIsManifold (F.connection 0) hc
      letI := unitRicciKernelT3Space (F.connection 0) hc
      let g' := unitRicciKernelMetric (F.connection 0) hc
      ∀ p : UnitRicciKernel (F.connection 0),
      let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
      let gC := g'.connectedComponentMetric p
      ∃ (N : Type u) (_ : TopologicalSpace N) (_ : T3Space N)
        (_ : ConnectedSpace N) (_ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) N)
        (_ : IsManifold (𝓡 2) ∞ N) (h : RiemannianMetric 2 N),
        MetricComplete h ∧
        ∃ e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ C,
          (∀ (z : N × ℝ) (a b : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
            gC.inner (e z) (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z a)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z b) =
                h.inner z.1 a.1 b.1 + a.2 * b.2) ∧
          (∀ y, (e.symm y).2 = unitRicciKernelCoordinate (F.connection 0) f y.1) := by
  obtain ⟨hc, hcard, hg⟩ := exists_complete_nullCover_coordinate hC F hoperator hnonflat
    hcomplete f hf hsol x v w hv hw hvw hzero
  refine ⟨hc, hcard, ?_⟩
  let := unitRicciKernelChartedSpace (F.connection 0) hc
  let := unitRicciKernelIsManifold (F.connection 0) hc
  let := unitRicciKernelT3Space (F.connection 0) hc
  dsimp only
  intro p
  exact exists_connectedComponent_productIsometry
    (unitRicciKernelMetric (F.connection 0) hc).leviCivitaData
    hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.1 p

end PoincareConjecture.RicciFlow.Splitting
