import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Metric.Distortion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Topology.Embedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Metric.CompactCarrier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SpatialEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.MeasureComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.RadiusSqueeze

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}

theorem eventually_volume_image_bounds
    (hconv : M23TerminalMetricConvergence G e)
    {U : Set G.limit.carrier.carrier} (hU : IsOpen U)
    (hcompact : IsCompact (closure U)) {C : ℝ} (hC : 1 < C) :
    ∀ᶠ k in atTop,
      calibratedMetricVolume ((S.term (G.subsequence k)).flow.flow.metric 0)
          ((fun x ↦ ((e k).toFun (0, x)).2) '' U) ≤
        ENNReal.ofReal C ^ 3 * calibratedMetricVolume (G.limit.flow.flow.metric 0) U ∧
      calibratedMetricVolume (G.limit.flow.flow.metric 0) U ≤
        ENNReal.ofReal C ^ 3 *
          calibratedMetricVolume ((S.term (G.subsequence k)).flow.flow.metric 0)
            ((fun x ↦ ((e k).toFun (0, x)).2) '' U) := by
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  filter_upwards [eventually_ge_atTop j,
    hconv.eventually_tangentNorm_bounds_on_compact hcompact hC] with k hk hmetric
  let E := (e k).spatialHomeomorph (mem_Iic.mpr le_rfl) (G.exhaustion_open k)
  let g := G.limit.flow.flow.metric 0
  let h := (S.term (G.subsequence k)).flow.flow.metric 0
  have hUE : U ⊆ E.source := subset_closure.trans (hj.trans (hmono hk))
  have hE : ContMDiffOn (𝓡 3) (𝓡 3) 1 E E.source :=
    ((e k).spatialHomeomorph_contMDiffOn (mem_Iic.mpr le_rfl)
      (G.exhaustion_open k)).of_le (by simp)
  have hEi : ContMDiffOn (𝓡 3) (𝓡 3) 1 E.symm E.target :=
    ((e k).spatialHomeomorph_symm_contMDiffOn (mem_Iic.mpr le_rfl)
      (G.exhaustion_open k)).of_le (by simp)
  have hEd : E.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨hE.mdifferentiableOn one_ne_zero, hEi.mdifferentiableOn one_ne_zero⟩
  have hf : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      h.tangentNorm (E x) (mfderiv (𝓡 3) (𝓡 3) E x v) ≤ C * g.tangentNorm x v :=
    fun x hx v ↦ (hmetric x (subset_closure hx) v).1
  have hb : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      g.tangentNorm x v ≤ C * h.tangentNorm (E x) (mfderiv (𝓡 3) (𝓡 3) E x v) :=
    fun x hx v ↦ (hmetric x (subset_closure hx) v).2
  have hu := g.volumeMeasure_image_le_of_tangentNorm_le h E hU hUE hE
    (zero_lt_one.trans hC) hf hU.measurableSet (Subset.refl U)
  have him : IsOpen (E '' U) := E.isOpen_image_of_subset_source hU hUE
  have hinv := g.inverse_tangentNorm_le_of_le h E hEd hUE hb
  have hl := h.volumeMeasure_image_le_of_tangentNorm_le g E.symm him
    (by rintro _ ⟨x, hx, rfl⟩; exact E.map_source (hUE hx))
    hEi (zero_lt_one.trans hC) hinv him.measurableSet (Subset.refl _)
  have hback : E.symm '' (E '' U) = U := by
    rw [image_image]
    exact Set.EqOn.image_eq_self (fun x hx ↦ E.left_inv (hUE hx))
  rw [hback] at hl
  simpa only [calibratedMetricVolume_eq_volumeMeasure, g, h, E,
    NormalizedKappaSpacetimeEmbedding.spatialHomeomorph_apply] using And.intro hu hl

theorem tendsto_volume_image_of_isCompact_closure
    (hconv : M23TerminalMetricConvergence G e)
    {U : Set G.limit.carrier.carrier} (hU : IsOpen U)
    (hcompact : IsCompact (closure U)) :
    Tendsto (fun k ↦
      calibratedMetricVolume ((S.term (G.subsequence k)).flow.flow.metric 0)
        ((fun x ↦ ((e k).toFun (0, x)).2) '' U)) atTop
      (𝓝 (calibratedMetricVolume (G.limit.flow.flow.metric 0) U)) :=
  Poincare.tendsto_of_ball_volume_radius_squeeze
    (V := fun _ ↦ calibratedMetricVolume (G.limit.flow.flow.metric 0) U)
    (r := 0) 3 continuousAt_const
    (fun _ hC ↦ (hconv.eventually_volume_image_bounds hU hcompact hC).mono fun _ h ↦ h.1)
    (fun _ hC ↦ (hconv.eventually_volume_image_bounds hU hcompact hC).mono fun _ h ↦ h.2)

theorem tendsto_cap_volume_image
    (hconv : M23TerminalMetricConvergence G e)
    (A : CapCertificate (G.limit.flow.flow.metric 0)) :
    Tendsto (fun k ↦
      calibratedMetricVolume ((S.term (G.subsequence k)).flow.flow.metric 0)
        ((fun x ↦ ((e k).toFun (0, x)).2) '' A.carrier)) atTop
      (𝓝 (calibratedMetricVolume (G.limit.flow.flow.metric 0) A.carrier)) :=
  hconv.tendsto_volume_image_of_isCompact_closure A.carrier_open
    (A.isCompact_closure_carrier (G.limit.flow.complete 0 le_rfl))

end M23TerminalMetricConvergence

end PoincareConjecture
