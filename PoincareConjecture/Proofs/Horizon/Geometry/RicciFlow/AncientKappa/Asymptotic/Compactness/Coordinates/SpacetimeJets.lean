import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.BilinearJetConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricFamily.PullbackCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Embedding.TimeIndependent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

theorem pullbackCoefficients_eq_of_eventuallyEq
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {f h : EuclideanSpace ℝ (Fin n) → M}
    {x : EuclideanSpace ℝ (Fin n)} (heq : f =ᶠ[𝓝 x] h) :
    g.pullbackCoefficients f x = g.pullbackCoefficients h x := by
  ext v w
  change g.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w) =
    g.inner (h x) (mfderiv (𝓡 n) (𝓡 n) h x v) (mfderiv (𝓡 n) (𝓡 n) h x w)
  rw [heq.mfderiv_eq, heq.self_of_nhds]

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

noncomputable def spatialSpacetimeCoefficients
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (q : G.limitCarrier.carrier) (k : ℕ) :
    ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  fun z => ((S.flow (G.subsequence k)).metricAt z.1).pullbackCoefficients
    (fun y => ((G.embedding k).toFun (0, (extChartAt (𝓡 n) q).symm y)).2) z.2

theorem spatialSpacetimeCoefficients_eq
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    (q : G.limitCarrier.carrier) (k : ℕ) {z : ℝ × EuclideanSpace ℝ (Fin n)}
    (ht : z.1 ∈ Ioo a b) (hy : z.2 ∈ (extChartAt (𝓡 n) q).target)
    (hs : (extChartAt (𝓡 n) q).symm z.2 ∈ G.exhaustion k) :
    G.spatialSpacetimeCoefficients q k z = G.pulledChartCoefficients q k z.1 z.2 := by
  apply RiemannianMetric.pullbackCoefficients_eq_of_eventuallyEq
  have hc := ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds hy)).continuousAt
  filter_upwards [hc.preimage_mem_nhds ((G.exhaustion_open k).mem_nhds hs)] with y hys
  exact (G.embedding k).spatial_eq_of_mem hzero ht hys

theorem contDiffAt_spatialSpacetimeCoefficients
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    (q : G.limitCarrier.carrier) (k : ℕ) {z : ℝ × EuclideanSpace ℝ (Fin n)}
    (ht : z.1 ∈ Ioo a b) (hy : z.2 ∈ (extChartAt (𝓡 n) q).target)
    (hs : (extChartAt (𝓡 n) q).symm z.2 ∈ G.exhaustion k) :
    ContDiffAt ℝ ∞ (G.spatialSpacetimeCoefficients q k) z := by
  exact (S.flow (G.subsequence k)).flow.smooth.contDiffAt_spacetime_pullbackCoefficients
    isOpen_Ioo
    (((G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hzero hs).comp z.2
      ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds hy))) ht

theorem spatialSpacetimeCoefficients_basis_jet_eq
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    (q : G.limitCarrier.carrier) (k r : ℕ) (i j : Fin n)
    {z : ℝ × EuclideanSpace ℝ (Fin n)}
    (ht : z.1 ∈ Ioo a b) (hy : z.2 ∈ (extChartAt (𝓡 n) q).target)
    (hs : (extChartAt (𝓡 n) q).symm z.2 ∈ G.exhaustion k) :
    iteratedFDeriv ℝ r (fun y => G.spatialSpacetimeCoefficients q k y
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) z =
    iteratedFDeriv ℝ r (G.limitCarrier.coordinateCoefficient q
      (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)) i j) z := by
  have hc := ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds hy)).continuousAt
  apply Filter.EventuallyEq.eq_of_nhds
  apply Filter.EventuallyEq.iteratedFDeriv
  filter_upwards [continuousAt_fst.preimage_mem_nhds (isOpen_Ioo.mem_nhds ht),
    continuousAt_snd.preimage_mem_nhds ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds hy),
    (hc.comp continuousAt_snd).preimage_mem_nhds ((G.exhaustion_open k).mem_nhds hs)]
      with p hpt hpy hps
  rw [G.spatialSpacetimeCoefficients_eq hzero q k hpt hpy hps]
  exact G.pulledChartCoefficients_basis_eq q k p.1 hpt hpy hps i j

theorem locally_eventually_contDiff_spatialSpacetimeCoefficients
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    (q : G.limitCarrier.carrier) :
    ∀ z ∈ Ioo a b ×ˢ (extChartAt (𝓡 n) q).target, ∃ W, IsOpen W ∧ z ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (G.spatialSpacetimeCoefficients q k) W := by
  intro z hz
  obtain ⟨s, hs⟩ := G.exists_exhaustion_superset (isCompact_singleton
    (x := (extChartAt (𝓡 n) q).symm z.2))
  let V := (extChartAt (𝓡 n) q).target ∩
    (extChartAt (𝓡 n) q).symm ⁻¹' G.exhaustion s
  have hV : IsOpen V := (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
    (isOpen_extChartAt_target (I := 𝓡 n) q) (G.exhaustion_open s)
  refine ⟨Ioo a b ×ˢ V, isOpen_Ioo.prod hV, ⟨hz.1, hz.2, hs (mem_singleton _)⟩, ?_⟩
  filter_upwards [eventually_ge_atTop s] with k hk p hp
  exact (G.contDiffAt_spatialSpacetimeCoefficients hzero q k hp.1 hp.2.1
    (G.exhaustion_monotone hk hp.2.2)).contDiffWithinAt

theorem tendstoUniformlyOn_spatialSpacetimeCoefficients_jets
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    (q : G.limitCarrier.carrier) (r : ℕ)
    {K : Set (ℝ × EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKU : K ⊆ Ioo a b ×ˢ (extChartAt (𝓡 n) q).target) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ r (G.spatialSpacetimeCoefficients q k))
      (iteratedFDeriv ℝ r (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        (G.limitFlow.metricAt z.1).pullbackCoefficients (extChartAt (𝓡 n) q).symm z.2)) atTop K := by
  let c := extChartAt (𝓡 n) q
  have hc : ContinuousOn (fun z : ℝ × EuclideanSpace ℝ (Fin n) => c.symm z.2) K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.comp continuous_snd.continuousOn
      (fun z hz => (hKU hz).2)
  obtain ⟨s, hs⟩ := G.exists_exhaustion_superset (hK.image_of_continuousOn hc)
  apply Poincare.Analysis.Calculus.tendstoUniformlyOn_bilinear_jets_of_basis_entries
  · filter_upwards [eventually_ge_atTop s] with k hk z hz
    exact G.contDiffAt_spatialSpacetimeCoefficients hzero q k (hKU hz).1 (hKU hz).2
      (G.exhaustion_monotone hk (hs (mem_image_of_mem _ hz)))
  · intro z hz
    exact G.limitFlow.flow.smooth.contDiffAt_spacetime_pullbackCoefficients isOpen_Ioo
      ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds (hKU hz).2)) (hKU hz).1
  · intro i j
    apply (G.tendstoUniformlyOn_coordinate_metricJet q r i j K hK
      (fun z hz => (hKU hz).1) (fun z hz => (hKU hz).2)).congr
    filter_upwards [eventually_ge_atTop s] with k hk z hz
    exact (G.spatialSpacetimeCoefficients_basis_jet_eq hzero q k r i j (hKU hz).1 (hKU hz).2
      (G.exhaustion_monotone hk (hs (mem_image_of_mem _ hz)))).symm

end PoincareConjecture.PointedGeometricConvergence
