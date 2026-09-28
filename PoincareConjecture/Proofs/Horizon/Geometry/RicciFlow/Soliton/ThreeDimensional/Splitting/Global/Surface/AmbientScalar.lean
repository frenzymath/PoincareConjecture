import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.SourceProduct
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.Normalization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.FactorCurvature.Flow

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow.Splitting

open RiemannianMetric

private theorem scalarCurvature_eq_of_metric_eq
    {n : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    {g h : RiemannianMetric n N} (D : LeviCivitaData g) (E : LeviCivitaData h)
    (heq : g = h) (x : N) : D.scalarCurvature x = E.scalarCurvature x := by
  subst h
  simp only [LeviCivitaData.scalarCurvature, LeviCivitaData.ricci, D.horizon_curvatureTensor_eq E]

variable {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
  [ConnectedSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem CanonicalAncientRoundProduct.scalarCurvature_zero
    {F : RicciFlow 3 M (Iic 0)} {r φ : M → ℝ} {κ : ℝ}
    {hr : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r}
    {hu : HasUnitGradient (F.connection 0) r}
    (hprod : CanonicalAncientRoundProduct F hr hu φ κ)
    (hc : MetricComplete (F.metric 0)) (hz : HasZeroHessian (F.connection 0) r)
    (x : M) : (F.connection 0).scalarCurvature x = 1 := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun y (_ : y ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hu y
  letI := openLevelSetChartedSpace hr (⊤ : Opens M) hreg 2 0
  letI := isManifold_openLevelSet hr (⊤ : Opens M) hreg 2 0
  obtain ⟨hconn, A, _, hmetric, ⟨cert⟩, hφ, hsol, _⟩ := hprod
  letI : ConnectedSpace (zeroLevelSet r) := hconn
  letI : CompactSpace (zeroLevelSet r) := cert.compact
  have hA (y : zeroLevelSet r) : (A.flow.connection 0).scalarCurvature y = 1 := by
    have h := (A.flow.connection 0).scalar_eq_twice_scale_of_compact_round_soliton
      hφ hsol (cert.round_at_all_times 0 le_rfl) y
    norm_num at h
    exact h
  let h := regularLevelMetric hr (⊤ : Opens M) hreg 0 (F.metric 0)
  have hh (y : zeroLevelSet r) : h.leviCivitaData.scalarCurvature y = 1 :=
    (scalarCurvature_eq_of_metric_eq (A.flow.connection 0) h.leviCivitaData hmetric y).symm.trans
      (hA y)
  obtain ⟨_, _, _, Φ, e, _, _, _, _, _, hscalar, _⟩ :=
    exists_parallelGradient_productIsometry_curvature hc hr hu hz
  exact (hscalar x).symm.trans (hh (e.symm x).1)

end PoincareConjecture.RicciFlow.Splitting

namespace PoincareConjecture.ShrinkingSolitonFlow

open RicciFlow.Splitting RiemannianMetric

variable {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
  [ConnectedSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S)

theorem scalarCurvature_minus_one_eq_one_of_null_plane
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : S.metric.inner x v v = 1) (hw : S.metric.inner x w w = 1)
    (hvw : S.metric.inner x v w = 0)
    (hzero : S.connection.curvatureTensor x v w v w = 0) :
    ∀ y : M, (G.flow.connection (-1)).scalarCurvature y = 1 := by
  obtain ⟨hc, hcard, hproducts⟩ :=
    G.exists_nullCover_component_canonicalAncientRound_product hP x v w hv hw hvw hzero
  obtain ⟨hc', _, hgeom⟩ :=
    G.exists_complete_nullCover_coordinate hP.curvature x v w hv hw hvw hzero
  letI := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
  letI := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
  letI := unitRicciKernelT2Space_of_covering hc
  letI := unitRicciKernelT3Space (G.ancientSourceFlow.connection 0) hc
  letI : MeasurableSpace (UnitRicciKernel (G.ancientSourceFlow.connection 0)) :=
    borel (UnitRicciKernel (G.ancientSourceFlow.connection 0))
  letI : BorelSpace (UnitRicciKernel (G.ancientSourceFlow.connection 0)) := ⟨rfl⟩
  obtain ⟨hc0, hr, hu, hz, _⟩ := hgeom
  intro y
  have hnonempty : (unitRicciKernelProjection (G.ancientSourceFlow.connection 0) ⁻¹'
      {y}).Nonempty := Set.nonempty_of_ncard_ne_zero (by
    change Nat.card (unitRicciKernelProjection (G.ancientSourceFlow.connection 0) ⁻¹'
      {y}) ≠ 0
    rw [hcard y]
    norm_num)
  obtain ⟨p, hp⟩ := hnonempty
  change unitRicciKernelProjection (G.ancientSourceFlow.connection 0) p = y at hp
  let L := unitRicciKernelFlow G.ancientSourceFlow hc
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
  let F := L.restrictComponent p
  letI : SecondCountableTopology C := (F.metric 0).secondCountableTopology
  obtain ⟨_, hrC, huC, hprod⟩ := hproducts p
  obtain ⟨_, hcomplete, _, _, hzC⟩ :=
    connectedComponent_complete_parallel_coordinate (L.connection 0) hr hu hz hc0 p
  let q : C := ⟨p, mem_connectedComponent⟩
  have hscalar := hprod.scalarCurvature_zero hcomplete hzC q
  rw [L.restrictComponent_scalarCurvature p 0 q,
    unitRicciKernelFlow_scalarCurvature] at hscalar
  change (G.ancientSourceFlow.connection 0).scalarCurvature
    (unitRicciKernelProjection (G.ancientSourceFlow.connection 0) p) = 1 at hscalar
  rw [hp] at hscalar
  have heq : G.ancientSourceFlow.metric 0 = G.flow.metric (-1) :=
    G.ancientSourceFlow_metric_zero.trans G.at_minus_one.symm
  exact (RicciFlow.Splitting.scalarCurvature_eq_of_metric_eq
    (G.ancientSourceFlow.connection 0) (G.flow.connection (-1)) heq y).symm.trans hscalar

include G in
theorem soliton_scalarCurvature_eq_one_of_null_plane
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : S.metric.inner x v v = 1) (hw : S.metric.inner x w w = 1)
    (hvw : S.metric.inner x v w = 0)
    (hzero : S.connection.curvatureTensor x v w v w = 0) :
    ∀ y : M, S.connection.scalarCurvature y = 1 := by
  intro y
  exact (RicciFlow.Splitting.scalarCurvature_eq_of_metric_eq
    (G.flow.connection (-1)) S.connection G.at_minus_one y).symm.trans
      (G.scalarCurvature_minus_one_eq_one_of_null_plane hP x v w hv hw hvw hzero y)

end PoincareConjecture.ShrinkingSolitonFlow
