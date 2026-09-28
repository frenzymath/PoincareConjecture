import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinarySpatialJets

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

theorem ordinaryChapter11_uniform_spatial_metricJets
    (p : ℕ → (G).point) (hpositive : ∀ k, 0 < (G).scalar (p k))
    (hdiverges : Tendsto (fun k => (G).scalar (p k)) atTop atTop) {J : Set ℝ}
    (C : GeneralizedBlowupConvergence
      (fixedFlowBlowupSequence (G) p hpositive hdiverges) J)
    (hJ : UniqueDiffOn ℝ J) (q : C.limit.sliceCarrier.carrier) (j r : ℕ)
    (K : Set (ℝ × EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K)
    (hdom : K ⊆ {z | z ∈ blowupMetricChartDomain C.limit q ∧
      (extChartAt (𝓡 3) q).symm z.2 ∈ C.exhaustion.space j})
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    letI := C.limit.carrier.topologicalSpace
    letI := C.limit.carrier.chartedSpace
    letI := C.limit.carrier.isManifold
    ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N,
      K ⊆ Icc (-C.exhaustion.time k) 0 ×ˢ (extChartAt (𝓡 3) q).target ∧
      ∀ a b : Fin 3, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ r
            (fun y => blowupPullbackCoefficient (C.embedding k) q a b (z.1, y)) z.2 -
          iteratedFDeriv ℝ r
            (fun y => FlowCarrier.coordinateCoefficient C.limit.carrier q
              (fun t x v w => (C.limit.flow.metric t).inner x v w) a b (z.1, y)) z.2‖ <
          epsilon := by
  let := C.limit.carrier.topologicalSpace
  let := C.limit.carrier.chartedSpace
  let := C.limit.carrier.isManifold
  let P := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := ℝ) (fun _ : Fin r =>
      ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3)))
  obtain ⟨N, hjN, hN⟩ := C.pullback_metric_CInfinity q j r K hK hdom epsilon hepsilon
  refine ⟨N, hjN, fun k hk => ⟨(hN k hk).1, fun a b z hz => ?_⟩⟩
  have hzk := (hN k hk).1 hz
  have hzl := (hdom hz).1
  let Dk := iteratedFDerivWithin ℝ r (blowupPullbackCoefficient (C.embedding k) q a b)
    (Icc (-C.exhaustion.time k) 0 ×ˢ (extChartAt (𝓡 3) q).target) z
  let D0 := iteratedFDerivWithin ℝ r
    (FlowCarrier.coordinateCoefficient C.limit.carrier q
      (fun t x v w => (C.limit.flow.metric t).inner x v w) a b)
    (blowupMetricChartDomain C.limit q) z
  have hsource : iteratedFDeriv ℝ r
      (fun y => blowupPullbackCoefficient (C.embedding k) q a b (z.1, y)) z.2 = P Dk :=
    ordinaryChapter11Cylinder_spatial_jet R (C.embedding k)
      (C.exhaustion.space_open k) (convex_Icc _ _).isPreconnected
      (uniqueDiffOn_Icc (neg_lt_zero.mpr (C.exhaustion.time_pos k))) q r a b z
      ⟨hzk.1, hzk.2, C.exhaustion.space_increasing (hjN.trans hk) (hdom hz).2⟩
  have hlimit : iteratedFDeriv ℝ r
      (fun y => FlowCarrier.coordinateCoefficient C.limit.carrier q
        (fun t x v w => (C.limit.flow.metric t).inner x v w) a b (z.1, y)) z.2 = P D0 :=
    iteratedFDeriv_prod_slice_eq_within (C.limit.flow.contDiffOn_chartMetric q a b)
      hJ (isOpen_extChartAt_target q) hzl.1 hzl.2 (WithTop.coe_le_coe.mpr le_top)
  rw [hsource, hlimit, ← map_sub]
  exact ((Dk - D0).norm_compContinuous_linearIsometry_le
    (fun _ : Fin r => LinearIsometry.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3)))).trans_lt
      ((hN k hk).2 a b z hz)

end PoincareConjecture.M34
