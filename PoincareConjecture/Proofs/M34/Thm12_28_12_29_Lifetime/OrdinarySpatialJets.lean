import PoincareConjecture.Proofs.M34.Mathlib.LocalSpatialJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryCylinderCoordinates
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.FixedFlowSequence
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.LimitMetricJets

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R

theorem ordinaryChapter11Cylinder_spatial_jet
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J}
    {origin scale : ℝ} {K : Set ℝ} {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder (G) L.sliceCarrier origin scale K U)
    (hU : IsOpen U) (hK : IsPreconnected K) (hKdiff : UniqueDiffOn ℝ K)
    (q : L.sliceCarrier.carrier) (r : ℕ) (a b : Fin 3)
    (p : ℝ × EuclideanSpace ℝ (Fin 3))
    (hp : p.1 ∈ K ∧ p.2 ∈ (extChartAt (𝓡 3) q).target ∧
      (extChartAt (𝓡 3) q).symm p.2 ∈ U) :
    iteratedFDeriv ℝ r (fun y => blowupPullbackCoefficient e q a b (p.1, y)) p.2 =
      (iteratedFDerivWithin ℝ r (blowupPullbackCoefficient e q a b)
        (K ×ˢ (extChartAt (𝓡 3) q).target) p).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3))) := by
  apply iteratedFDeriv_prod_slice_eq_within_of_open_subset
    (ordinaryChapter11Cylinder_coefficient_contDiffOn R e hU hK hp.1 q a b)
    hKdiff ((continuousOn_extChartAt_symm q).isOpen_inter_preimage
      (isOpen_extChartAt_target q) hU) inter_subset_left hp.1 hp.2
  exact WithTop.coe_le_coe.mpr le_top

theorem ordinaryChapter11_tendsto_spatial_metricJet
    (p : ℕ → (G).point) (hpositive : ∀ k, 0 < (G).scalar (p k))
    (hdiverges : Tendsto (fun k => (G).scalar (p k)) atTop atTop) {J : Set ℝ}
    (C : GeneralizedBlowupConvergence
      (fixedFlowBlowupSequence (G) p hpositive hdiverges) J)
    (hJ : UniqueDiffOn ℝ J) (q : C.limit.sliceCarrier.carrier)
    (r : ℕ) (a b : Fin 3) (z : ℝ × EuclideanSpace ℝ (Fin 3))
    (hz : z ∈ blowupMetricChartDomain C.limit q) :
    letI := C.limit.carrier.topologicalSpace
    letI := C.limit.carrier.chartedSpace
    letI := C.limit.carrier.isManifold
    Tendsto (fun k => iteratedFDeriv ℝ r
      (fun y => blowupPullbackCoefficient (C.embedding k) q a b (z.1, y)) z.2)
      atTop (𝓝 (iteratedFDeriv ℝ r
        (fun y => FlowCarrier.coordinateCoefficient C.limit.carrier q
          (fun t x v w => (C.limit.flow.metric t).inner x v w) a b (z.1, y)) z.2)) := by
  let := C.limit.carrier.topologicalSpace
  let := C.limit.carrier.chartedSpace
  let := C.limit.carrier.isManifold
  let P := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := ℝ) (fun _ : Fin r =>
      ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3)))
  have h := P.continuous.continuousAt.tendsto.comp
    (C.tendsto_coordinate_metricJetWithin q r a b z hz)
  have hlim : iteratedFDeriv ℝ r
      (fun y => FlowCarrier.coordinateCoefficient C.limit.carrier q
        (fun t x v w => (C.limit.flow.metric t).inner x v w) a b (z.1, y)) z.2 =
      P (iteratedFDerivWithin ℝ r
        (FlowCarrier.coordinateCoefficient C.limit.carrier q
          (fun t x v w => (C.limit.flow.metric t).inner x v w) a b)
        (blowupMetricChartDomain C.limit q) z) :=
    iteratedFDeriv_prod_slice_eq_within (C.limit.flow.contDiffOn_chartMetric q a b)
      hJ (isOpen_extChartAt_target q) hz.1 hz.2 (WithTop.coe_le_coe.mpr le_top)
  rw [← hlim] at h
  apply h.congr'
  obtain ⟨j, hj⟩ := C.exists_exhaustion_superset
    (isCompact_singleton (x := (extChartAt (𝓡 3) q).symm z.2))
  have htime := C.exhaustion.time_cofinal {z.1} isCompact_singleton
    (singleton_subset_iff.mpr hz.1)
  filter_upwards [eventually_ge_atTop j, htime] with k hk htk
  exact (ordinaryChapter11Cylinder_spatial_jet R (C.embedding k)
    (C.exhaustion.space_open k) (convex_Icc _ _).isPreconnected
    (uniqueDiffOn_Icc (neg_lt_zero.mpr (C.exhaustion.time_pos k))) q r a b z
    ⟨htk (mem_singleton _), hz.2,
      C.exhaustion.space_increasing hk (hj (mem_singleton _))⟩).symm

end PoincareConjecture.M34
