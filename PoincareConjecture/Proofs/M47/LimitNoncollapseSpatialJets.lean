import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinarySpatialJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryRealization
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.FixedFlowSequence
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryCurvatureLimits










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)



theorem limitNoncollapse_included_spatial_metricJet
    (p : ℕ → (M34.ordinaryChapter11Flow (I := I) (F := F) R).point)
    (hpositive : ∀ k, 0 < (M34.ordinaryChapter11Flow (I := I) (F := F) R).scalar (p k))
    (hdiverges : Tendsto
      (fun k => (M34.ordinaryChapter11Flow (I := I) (F := F) R).scalar (p k))
      atTop atTop)
    {J : Set ℝ}
    (C : GeneralizedBlowupConvergence
      (M34.fixedFlowBlowupSequence (M34.ordinaryChapter11Flow (I := I) (F := F) R)
        p hpositive hdiverges) J)
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
  exact M34.ordinaryChapter11_tendsto_spatial_metricJet R p hpositive hdiverges
    C hJ q r a b z hz



theorem limitNoncollapse_included_curvature_readout
    (p : ℕ → (M34.ordinaryChapter11Flow (I := I) (F := F) R).point)
    (hpositive : ∀ k, 0 < (M34.ordinaryChapter11Flow (I := I) (F := F) R).scalar (p k))
    (hdiverges : Tendsto
      (fun k => (M34.ordinaryChapter11Flow (I := I) (F := F) R).scalar (p k))
      atTop atTop)
    {J : Set ℝ}
    (C : GeneralizedBlowupConvergence
      (M34.fixedFlowBlowupSequence (M34.ordinaryChapter11Flow (I := I) (F := F) R)
        p hpositive hdiverges) J)
    (hJ : UniqueDiffOn ℝ J) (x : C.limit.sliceCarrier.carrier) :
    letI := C.limit.carrier.topologicalSpace
    letI := C.limit.carrier.chartedSpace
    letI := C.limit.carrier.isManifold
    (Tendsto (fun k =>
      (M34.ordinaryChapter11Flow (I := I) (F := F) R).scalar
        ((C.embedding k).pointMap 0
          ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩ x) /
        (M34.ordinaryChapter11Flow (I := I) (F := F) R).scalar
          (p (C.subsequence k))) atTop
      (𝓝 ((C.limit.flow.connection 0).scalarCurvature x))) ∧
    Tendsto (fun k =>
      (M34.ordinaryChapter11Flow (I := I) (F := F) R).curvatureNorm
        ((C.embedding k).pointMap 0
          ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩ x) /
        (M34.ordinaryChapter11Flow (I := I) (F := F) R).scalar
          (p (C.subsequence k))) atTop
      (𝓝 ((C.limit.flow.connection 0).curvatureTensorNorm x)) := by
  exact M34.ordinaryChapter11_tendsto_curvatures_zero R p hpositive hdiverges
    C hJ x

end PoincareConjecture.M47
