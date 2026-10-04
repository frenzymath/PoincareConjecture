import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Calculus.LocalSpatialJets
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.LimitGeometry.Charts.CylinderCoordinates
open scoped PoincareMT.DeepHornSource

/-!
# Actual spatial metric jets at included limit times

Morgan--Tian Theorem 11.8, printed p. 272, and Claim 11.34, printed
pp. 288-289. The actual generalized-cylinder coefficient is smooth only
on the captured open source. Its spatial jet nevertheless equals the
restriction of the stored joint jet on the whole frozen chart target.

Read-only donors are `ordinaryChapter11Cylinder_spatial_jet` in M34
`Thm12_28_12_29_Lifetime/OrdinarySpatialJets.lean` and
`ordinaryChapter11_uniform_spatial_metricJets` in the adjacent
`UniformOrdinarySpatialJets.lean`. Here the original sequence may vary
both generalized flow and carrier, and unique differentiability of the
limit interval follows from its retained Ricci-flow data.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

/-- The source spatial jet is the frozen within jet restricted to spatial
directions at every included time; Theorem 11.8, printed p. 272. -/
theorem blowupPullbackCoefficient_spatial_jet
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J} {F : GeneralizedRicciFlowData.{u}}
    {I : SpacetimeInterval} {origin scale : ℝ} {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder F L.sliceCarrier origin scale I.domain U)
    (hU : IsOpen U) (q : L.sliceCarrier.carrier) (r : ℕ) (a b : Fin 3)
    (z : ℝ × EuclideanSpace ℝ (Fin 3))
    (hz : z.1 ∈ I.domain ∧ z.2 ∈ (extChartAt (𝓡 3) q).target ∧
      (extChartAt (𝓡 3) q).symm z.2 ∈ U) :
    iteratedFDeriv ℝ r (fun y => blowupPullbackCoefficient e q a b (z.1, y)) z.2 =
      (iteratedFDerivWithin ℝ r (blowupPullbackCoefficient e q a b)
        (I.domain ×ˢ (extChartAt (𝓡 3) q).target) z).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3))) := by
  apply iteratedFDeriv_prod_slice_eq_within_of_open_subset
    (blowupPullbackCoefficient_contDiffOn e hU q a b)
    (Proofs.M11.interval_uniqueDiffOn I)
    ((continuousOn_extChartAt_symm q).isOpen_inter_preimage
      (isOpen_extChartAt_target q) hU) inter_subset_left hz.1 hz.2
  exact WithTop.coe_le_coe.mpr le_top

set_option backward.isDefEq.respectTransparency false in
/-- Spatial jets of the actual generalized blowup converge uniformly on
captured compact sets, including time zero; Claim 11.34, printed pp. 288-289. -/
theorem blowup_uniform_spatial_metricJets
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (q : G.limit.sliceCarrier.carrier) (j r : ℕ)
    (K : Set (ℝ × EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K)
    (hdom : K ⊆ {z | z ∈ blowupMetricChartDomain G.limit q ∧
      (extChartAt (𝓡 3) q).symm z.2 ∈ G.exhaustion.space j})
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N,
      K ⊆ Icc (-G.exhaustion.time k) 0 ×ˢ (extChartAt (𝓡 3) q).target ∧
      ∀ a b : Fin 3, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ r
            (fun y => blowupPullbackCoefficient (G.embedding k) q a b (z.1, y)) z.2 -
          iteratedFDeriv ℝ r
            (fun y => FlowCarrier.coordinateCoefficient G.limit.carrier q
              (fun t x v w => (G.limit.flow.metric t).inner x v w) a b (z.1, y)) z.2‖ <
          epsilon := by
  let P := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := ℝ) (fun _ : Fin r =>
      ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3)))
  let Jtime : SpacetimeInterval := ⟨J, G.limit.flow.interval, G.limit.flow.nontrivial⟩
  have hJ := Proofs.M11.interval_uniqueDiffOn Jtime
  have hcoeff := contDiffOn_clock_pullbackCoefficients_of_smoothFamily
    G.limit.flow.smooth (isOpen_extChartAt_target q)
    (contMDiffOn_extChartAt_symm (n := ∞) q)
    (contDiff_id : ContDiff ℝ ∞ (fun t : ℝ => t)) (fun _ ht => ht)
  have hreference (a b : Fin 3) : ContDiffOn ℝ ∞
      (FlowCarrier.coordinateCoefficient G.limit.carrier q
        (fun t x v w => (G.limit.flow.metric t).inner x v w) a b)
      (blowupMetricChartDomain G.limit q) :=
    (hcoeff.clm_apply (contDiffOn_const (c := EuclideanSpace.basisFun (Fin 3) ℝ a))).clm_apply
      (contDiffOn_const (c := EuclideanSpace.basisFun (Fin 3) ℝ b))
  obtain ⟨N, hjN, hN⟩ := G.pullback_metric_CInfinity q j r K hK hdom epsilon hepsilon
  refine ⟨N, hjN, fun k hk => ⟨(hN k hk).1, fun a b z hz => ?_⟩⟩
  have hzk := (hN k hk).1 hz
  have hzl := (hdom hz).1
  let Itime : SpacetimeInterval := {
    domain := Icc (-G.exhaustion.time k) 0
    ordConnected := ordConnected_Icc
    nontrivial := ⟨-G.exhaustion.time k,
      ⟨le_rfl, neg_nonpos.mpr (G.exhaustion.time_pos k).le⟩,
      0, ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩,
      (neg_lt_zero.mpr (G.exhaustion.time_pos k)).ne⟩ }
  let Dk := iteratedFDerivWithin ℝ r (blowupPullbackCoefficient (G.embedding k) q a b)
    (Icc (-G.exhaustion.time k) 0 ×ˢ (extChartAt (𝓡 3) q).target) z
  let D0 := iteratedFDerivWithin ℝ r
    (FlowCarrier.coordinateCoefficient G.limit.carrier q
      (fun t x v w => (G.limit.flow.metric t).inner x v w) a b)
    (blowupMetricChartDomain G.limit q) z
  have hsource : iteratedFDeriv ℝ r
      (fun y => blowupPullbackCoefficient (G.embedding k) q a b (z.1, y)) z.2 = P Dk :=
    blowupPullbackCoefficient_spatial_jet (I := Itime) (G.embedding k)
      (G.exhaustion.space_open k) q r a b z
      ⟨hzk.1, hzk.2, G.exhaustion.space_increasing (hjN.trans hk) (hdom hz).2⟩
  have hlimit : iteratedFDeriv ℝ r
      (fun y => FlowCarrier.coordinateCoefficient G.limit.carrier q
        (fun t x v w => (G.limit.flow.metric t).inner x v w) a b (z.1, y)) z.2 = P D0 :=
    iteratedFDeriv_prod_slice_eq_within (hreference a b) hJ
      (isOpen_extChartAt_target q) hzl.1 hzl.2 (WithTop.coe_le_coe.mpr le_top)
  rw [hsource, hlimit, ← map_sub]
  exact ((Dk - D0).norm_compContinuous_linearIsometry_le
    (fun _ : Fin r => LinearIsometry.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3)))).trans_lt
      ((hN k hk).2 a b z hz)

end PoincareMT.M32
