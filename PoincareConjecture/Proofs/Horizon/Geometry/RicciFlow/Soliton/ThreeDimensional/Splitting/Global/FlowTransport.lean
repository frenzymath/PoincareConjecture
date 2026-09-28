import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.FlowExtension
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.AmbientScalar









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.ShrinkingSolitonFlow

open RicciFlow.Splitting RiemannianMetric

variable {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S)



def nullCoverNegativeFlow
    (hc : IsCoveringMap (unitRicciKernelProjection (G.ancientSourceFlow.connection 0))) :
    letI := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
    letI := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
    RicciFlow 3 (UnitRicciKernel (G.ancientSourceFlow.connection 0)) (Iio 0) := by
  let := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
  let := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
  exact G.flow.pullbackWithConnection
    (unitRicciKernelProjection (G.ancientSourceFlow.connection 0))
    (unitRicciKernelProjection_isLocalDiffeomorph (G.ancientSourceFlow.connection 0) hc)
    (fun t => ((G.flow.metric t).pullbackOfLocalDiffeomorph
      (unitRicciKernelProjection (G.ancientSourceFlow.connection 0))
      (unitRicciKernelProjection_isLocalDiffeomorph
        (G.ancientSourceFlow.connection 0) hc)).leviCivitaData)

theorem nullCoverNegativeFlow_inner
    (hc : IsCoveringMap (unitRicciKernelProjection (G.ancientSourceFlow.connection 0)))
    (t : ℝ) (p : UnitRicciKernel (G.ancientSourceFlow.connection 0)) :
    letI := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
    letI := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
    ∀ v w : TangentSpace (𝓡 3) p,
      ((G.nullCoverNegativeFlow hc).metric t).inner p v w =
        (G.flow.metric t).inner (unitRicciKernelProjection (G.ancientSourceFlow.connection 0) p)
          (mfderiv (𝓡 3) (𝓡 3)
            (unitRicciKernelProjection (G.ancientSourceFlow.connection 0)) p v)
          (mfderiv (𝓡 3) (𝓡 3)
            (unitRicciKernelProjection (G.ancientSourceFlow.connection 0)) p w) := by
  let := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
  let := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
  intro v w
  rfl

theorem nullCoverNegativeFlow_component_inner
    (hc : IsCoveringMap (unitRicciKernelProjection (G.ancientSourceFlow.connection 0)))
    (p : UnitRicciKernel (G.ancientSourceFlow.connection 0)) :
    letI := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
    letI := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
    let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
    let proj : C → M := fun q => unitRicciKernelProjection (G.ancientSourceFlow.connection 0) q.1
    ∀ (t : ℝ) (q : C) (v w : TangentSpace (𝓡 3) q),
      (((G.nullCoverNegativeFlow hc).restrictComponent p).metric t).inner q v w =
        (G.flow.metric t).inner (proj q)
          (mfderiv (𝓡 3) (𝓡 3) proj q v) (mfderiv (𝓡 3) (𝓡 3) proj q w) := by
  let := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
  let := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
  intro C proj t q v w
  change _ = (G.flow.metric t).inner (proj q)
    (mfderiv (𝓡 3) (𝓡 3)
      (unitRicciKernelProjection (G.ancientSourceFlow.connection 0) ∘ (Subtype.val : C → _)) q v)
    (mfderiv (𝓡 3) (𝓡 3)
      (unitRicciKernelProjection (G.ancientSourceFlow.connection 0) ∘ (Subtype.val : C → _)) q w)
  rw [mfderiv_comp q
    ((unitRicciKernelProjection_isLocalDiffeomorph
      (G.ancientSourceFlow.connection 0) hc).mdifferentiable (by simp) q.1)
    ((Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) C).mdifferentiable (by simp) q)]
  rfl



theorem nullCoverNegativeFlow_metric_minus_one
    (hc : IsCoveringMap (unitRicciKernelProjection (G.ancientSourceFlow.connection 0))) :
    letI := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
    letI := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
    (G.nullCoverNegativeFlow hc).metric (-1) =
      unitRicciKernelMetric (G.ancientSourceFlow.connection 0) hc := by
  let := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
  let := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
  exact congrArg (fun g : RiemannianMetric 3 M => g.pullbackOfLocalDiffeomorph
    (unitRicciKernelProjection (G.ancientSourceFlow.connection 0))
    (unitRicciKernelProjection_isLocalDiffeomorph (G.ancientSourceFlow.connection 0) hc))
      (G.at_minus_one.trans G.ancientSourceFlow_metric_zero.symm)

theorem nullCoverNegativeFlow_ricci
    (hc : IsCoveringMap (unitRicciKernelProjection (G.ancientSourceFlow.connection 0)))
    (t : ℝ) (p : UnitRicciKernel (G.ancientSourceFlow.connection 0)) :
    letI := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
    letI := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
    ∀ v w : TangentSpace (𝓡 3) p,
      ((G.nullCoverNegativeFlow hc).connection t).ricci p v w =
        (G.flow.connection t).ricci
          (unitRicciKernelProjection (G.ancientSourceFlow.connection 0) p)
          (mfderiv (𝓡 3) (𝓡 3)
            (unitRicciKernelProjection (G.ancientSourceFlow.connection 0)) p v)
          (mfderiv (𝓡 3) (𝓡 3)
            (unitRicciKernelProjection (G.ancientSourceFlow.connection 0)) p w) := by
  let := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
  let := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
  intro v w
  exact ((G.nullCoverNegativeFlow hc).connection t).ricci_eq_of_local_isometry
    (G.flow.connection t) isOpen_univ
    (unitRicciKernelProjection_isLocalDiffeomorph
      (G.ancientSourceFlow.connection 0) hc).contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ p) v w

theorem nullCoverNegativeFlow_ricciNullity
    (hc : IsCoveringMap (unitRicciKernelProjection (G.ancientSourceFlow.connection 0)))
    (t : ℝ) (p : UnitRicciKernel (G.ancientSourceFlow.connection 0)) :
    letI := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
    letI := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
    ricciNullity ((G.nullCoverNegativeFlow hc).connection t) p =
      ricciNullity (G.flow.connection t)
        (unitRicciKernelProjection (G.ancientSourceFlow.connection 0) p) := by
  let := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
  let := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
  let proj := unitRicciKernelProjection (G.ancientSourceFlow.connection 0)
  let L := ((unitRicciKernelProjection_isLocalDiffeomorph
    (G.ancientSourceFlow.connection 0) hc).mfderivToContinuousLinearEquiv
      (by simp) p).toLinearEquiv
  have hker : ricciKernel (G.flow.connection t) (proj p) =
      (ricciKernel ((G.nullCoverNegativeFlow hc).connection t) p).map L.toLinearMap := by
    ext v
    rw [Submodule.mem_map_equiv, mem_ricciKernel, mem_ricciKernel]
    constructor
    · intro hv w
      rw [G.nullCoverNegativeFlow_ricci]
      change (G.flow.connection t).ricci (proj p) (L (L.symm v)) (L w) = 0
      rw [L.apply_symm_apply]
      exact hv _
    · intro hv w
      obtain ⟨z, rfl⟩ := L.surjective w
      have hz := hv z
      rw [G.nullCoverNegativeFlow_ricci] at hz
      change (G.flow.connection t).ricci (proj p) (L (L.symm v)) (L z) = 0 at hz
      simpa only [L.apply_symm_apply] using hz
  unfold ricciNullity
  rw [hker, LinearEquiv.finrank_map_eq]

theorem nullCoverNegativeFlow_scalarCurvature
    (hc : IsCoveringMap (unitRicciKernelProjection (G.ancientSourceFlow.connection 0)))
    (t : ℝ) (p : UnitRicciKernel (G.ancientSourceFlow.connection 0)) :
    letI := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
    letI := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
    ((G.nullCoverNegativeFlow hc).connection t).scalarCurvature p =
      (G.flow.connection t).scalarCurvature
        (unitRicciKernelProjection (G.ancientSourceFlow.connection 0) p) := by
  let := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
  let := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
  exact ((G.nullCoverNegativeFlow hc).connection t).scalarCurvature_eq_of_local_isometry
    (G.flow.connection t) isOpen_univ
    (unitRicciKernelProjection_isLocalDiffeomorph
      (G.ancientSourceFlow.connection 0) hc).contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ p)

theorem nullCoverNegativeFlow_nonnegativeCurvatureOperator_iff
    (hc : IsCoveringMap (unitRicciKernelProjection (G.ancientSourceFlow.connection 0)))
    (t : ℝ) (p : UnitRicciKernel (G.ancientSourceFlow.connection 0)) :
    letI := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
    letI := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
    ((G.nullCoverNegativeFlow hc).connection t).NonnegativeCurvatureOperator p ↔
      (G.flow.connection t).NonnegativeCurvatureOperator
        (unitRicciKernelProjection (G.ancientSourceFlow.connection 0) p) := by
  let := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
  let := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
  exact ((G.nullCoverNegativeFlow hc).connection t).nonnegativeCurvatureOperator_iff_of_local_isometry
    (G.flow.connection t) isOpen_univ
    (unitRicciKernelProjection_isLocalDiffeomorph
      (G.ancientSourceFlow.connection 0) hc).contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ p)



theorem nullCoverNegativeFlow_component_inner_eq_transverse_scale
    (hC : RicciFlowCurvatureTheory.{u})
    (hc : IsCoveringMap (unitRicciKernelProjection (G.ancientSourceFlow.connection 0)))
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : S.metric.inner x v v = 1) (hw : S.metric.inner x w w = 1)
    (hvw : S.metric.inner x v w = 0)
    (hzero : S.connection.curvatureTensor x v w v w = 0)
    (hscalar : ∀ y : M, S.connection.scalarCurvature y = 1) :
    letI := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
    letI := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
    letI := unitRicciKernelT3Space (G.ancientSourceFlow.connection 0) hc
    let g := unitRicciKernelMetric (G.ancientSourceFlow.connection 0) hc
    let r := unitRicciKernelCoordinate (G.ancientSourceFlow.connection 0) S.potential
    MetricComplete g → ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r →
      HasUnitGradient g.leviCivitaData r → HasZeroHessian g.leviCivitaData r →
    ∀ p : UnitRicciKernel (G.ancientSourceFlow.connection 0),
      let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
      let rC : C → ℝ := r ∘ Subtype.val
      let F := (G.nullCoverNegativeFlow hc).restrictComponent p
      let A := (unitRicciKernelFlow G.ancientSourceFlow hc).restrictComponent p
      ∀ t < 0, ∀ (q : C) (a b : TangentSpace (𝓡 3) q),
        (F.metric t).inner q a b =
          (-t) * ((A.metric 0).inner q a b -
            mvfderiv (𝓡 3) rC q a * mvfderiv (𝓡 3) rC q b) +
              mvfderiv (𝓡 3) rC q a * mvfderiv (𝓡 3) rC q b := by
  let := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
  let := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
  let : T2Space (UnitRicciKernel (G.ancientSourceFlow.connection 0)) :=
    unitRicciKernelT2Space_of_covering hc
  let := unitRicciKernelT3Space (G.ancientSourceFlow.connection 0) hc
  intro g r hcomplete hr hu hz p C rC F A
  obtain ⟨hconn, _, hrC, huC, hzC⟩ :=
    connectedComponent_complete_parallel_coordinate g.leviCivitaData hr hu hz hcomplete p
  let : ConnectedSpace C := hconn
  let L := G.nullCoverNegativeFlow hc
  have hdimG := G.ricciNullity_eq_one_of_null_plane hC x v w hv hw hvw hzero
  have hdim (t : ℝ) (ht : t < 0) (q : C) : ricciNullity (F.connection t) q = 1 := by
    rw [restrictComponent_ricciNullity, G.nullCoverNegativeFlow_ricciNullity]
    exact hdimG t ht _
  have hR (t : ℝ) (ht : t < 0) (q : C) :
      (F.connection t).scalarCurvature q = -(t⁻¹) := by
    rw [RicciFlow.restrictComponent_scalarCurvature, G.nullCoverNegativeFlow_scalarCurvature]
    exact G.scalarCurvature_eq_neg_inv_of_initial_scalar_one hscalar t ht _
  have hsec (t : ℝ) (ht : t < 0) : (F.connection t).NonnegativeSectionalCurvature := by
    intro q a b
    apply (F.connection t).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator q
    apply (L.restrictComponent_nonnegativeCurvatureOperator_iff p t q).mpr
    apply (G.nullCoverNegativeFlow_nonnegativeCurvatureOperator_iff hc t q.1).mpr
    obtain ⟨E⟩ := G.self_similar t ht
    exact E.nonnegativeCurvatureOperator (abs_pos.mpr ht.ne) S.connection
      (G.flow.connection t) S.nonnegative_curvature _
  have hm : F.metric (-1) = A.metric 0 :=
    congrArg (fun g' => g'.connectedComponentMetric p) (G.nullCoverNegativeFlow_metric_minus_one hc)
  have hu' : HasUnitGradient (F.connection (-1)) rC := by
    change HasUnitGradient (F.metric (-1)).leviCivitaData rC
    rw [hm]
    exact huC
  have hz' : HasZeroHessian (F.connection (-1)) rC := by
    change HasZeroHessian (F.metric (-1)).leviCivitaData rC
    rw [hm]
    exact hzC
  intro t ht q a b
  simpa only [hm] using
    inner_eq_transverse_scale_on_negative_times hC F hsec
      (fun s hs y => (hdim s hs y).trans (hdim (-1) (by norm_num) y).symm)
      hR hrC hu' hz' t ht q a b



theorem nullCoverComponent_projection_inner_eq_transverse_scale
    (hC : RicciFlowCurvatureTheory.{u})
    (hc : IsCoveringMap (unitRicciKernelProjection (G.ancientSourceFlow.connection 0)))
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : S.metric.inner x v v = 1) (hw : S.metric.inner x w w = 1)
    (hvw : S.metric.inner x v w = 0)
    (hzero : S.connection.curvatureTensor x v w v w = 0)
    (hscalar : ∀ y : M, S.connection.scalarCurvature y = 1) :
    letI := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
    letI := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
    letI := unitRicciKernelT3Space (G.ancientSourceFlow.connection 0) hc
    let g := unitRicciKernelMetric (G.ancientSourceFlow.connection 0) hc
    let r := unitRicciKernelCoordinate (G.ancientSourceFlow.connection 0) S.potential
    MetricComplete g → ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r →
      HasUnitGradient g.leviCivitaData r → HasZeroHessian g.leviCivitaData r →
    ∀ p : UnitRicciKernel (G.ancientSourceFlow.connection 0),
      let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
      let rC : C → ℝ := r ∘ Subtype.val
      let proj : C → M := fun q =>
        unitRicciKernelProjection (G.ancientSourceFlow.connection 0) q.1
      let A := (unitRicciKernelFlow G.ancientSourceFlow hc).restrictComponent p
      ∀ t < 0, ∀ (q : C) (a b : TangentSpace (𝓡 3) q),
        (G.flow.metric t).inner (proj q)
          (mfderiv (𝓡 3) (𝓡 3) proj q a) (mfderiv (𝓡 3) (𝓡 3) proj q b) =
          (-t) * ((A.metric 0).inner q a b -
            mvfderiv (𝓡 3) rC q a * mvfderiv (𝓡 3) rC q b) +
              mvfderiv (𝓡 3) rC q a * mvfderiv (𝓡 3) rC q b := by
  let := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
  let := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
  let := unitRicciKernelT3Space (G.ancientSourceFlow.connection 0) hc
  intro g r hcomplete hr hu hz p C rC proj A t ht q a b
  exact (G.nullCoverNegativeFlow_component_inner hc p t q a b).symm.trans
    (G.nullCoverNegativeFlow_component_inner_eq_transverse_scale hC hc
      x v w hv hw hvw hzero hscalar hcomplete hr hu hz p t ht q a b)




theorem exists_nullCover_allNegative_transverse_scale
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
        let rC : C → ℝ := fun q => unitRicciKernelCoordinate
          (G.ancientSourceFlow.connection 0) S.potential q.1
        let F := (G.nullCoverNegativeFlow hc).restrictComponent p
        let A := (unitRicciKernelFlow G.ancientSourceFlow hc).restrictComponent p
        ∀ t < 0, ∀ (q : C) (a b : TangentSpace (𝓡 3) q),
          (F.metric t).inner q a b =
            (-t) * ((A.metric 0).inner q a b -
              mvfderiv (𝓡 3) rC q a * mvfderiv (𝓡 3) rC q b) +
                mvfderiv (𝓡 3) rC q a * mvfderiv (𝓡 3) rC q b := by
  obtain ⟨hc, hcard, hgeom⟩ :=
    G.exists_complete_nullCover_coordinate hP.curvature x v w hv hw hvw hzero
  refine ⟨hc, hcard, ?_⟩
  let := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
  let := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
  let := unitRicciKernelT3Space (G.ancientSourceFlow.connection 0) hc
  obtain ⟨hcomplete, hr, hu, hz, _⟩ := hgeom
  exact G.nullCoverNegativeFlow_component_inner_eq_transverse_scale hP.curvature hc
    x v w hv hw hvw hzero
    (G.soliton_scalarCurvature_eq_one_of_null_plane hP x v w hv hw hvw hzero)
    hcomplete hr hu hz

end PoincareConjecture.ShrinkingSolitonFlow
