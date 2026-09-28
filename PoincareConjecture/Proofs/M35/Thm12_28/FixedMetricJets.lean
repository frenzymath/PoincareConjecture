import PoincareConjecture.Proofs.M35.Thm12_28.CylinderCoordinates
import PoincareConjecture.Proofs.M35.Thm12_28.BlowupSequence










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization



noncomputable def fixedCylinderMetricCoefficient {J : Set ℝ}
    (F : RicciFlow 3 StandardCapSpace J) (C : GeneralizedSliceCarrier)
    (a Q : ℝ) (f : C.carrier → StandardCapSpace) (q : C.carrier)
    (i j : Fin 3) (p : ℝ × EuclideanSpace ℝ (Fin 3)) : ℝ :=
  let c := extChartAt (𝓡 3) q
  let D := mfderiv (𝓡 3) (𝓡 3) c.symm p.2
  let L := mfderiv (𝓡 3) (𝓡 3) f (c.symm p.2)
  Q * (F.metric (a + p.1 / Q)).inner (f (c.symm p.2))
    (L (D (EuclideanSpace.basisFun (Fin 3) ℝ i)))
    (L (D (EuclideanSpace.basisFun (Fin 3) ℝ j)))



theorem cylinder_coefficient_eq_fixed {J K : Set ℝ}
    (F : RicciFlow 3 StandardCapSpace J) {L : BlowupLimitFlow K}
    {a Q : ℝ} {I : Set ℝ} {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder (generalizedFlow F) L.sliceCarrier a Q I U)
    (hI : IsPreconnected I) (hU : IsOpen U) {s : ℝ} (hs : s ∈ I)
    (q : L.sliceCarrier.carrier) (i j : Fin 3)
    (p : ℝ × EuclideanSpace ℝ (Fin 3)) (hp : p.1 ∈ I)
    (hx : (extChartAt (𝓡 3) q).symm p.2 ∈ U) :
    blowupPullbackCoefficient e q i j p =
      fixedCylinderMetricCoefficient F L.sliceCarrier a Q
        (fun y => (e.forward s hs y).val) q i j p := by
  unfold blowupPullbackCoefficient fixedCylinderMetricCoefficient
  rw [dif_pos hp]
  exact cylinder_pullbackInner_eq_fixed F e hI hU hp hs hx _ _




theorem cylinder_coefficient_jet_eq_fixed {J K : Set ℝ}
    (F : RicciFlow 3 StandardCapSpace J) {L : BlowupLimitFlow K}
    {a Q : ℝ} {I : Set ℝ} {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder (generalizedFlow F) L.sliceCarrier a Q I U)
    (hI : IsPreconnected I) (hU : IsOpen U) {s : ℝ} (hs : s ∈ I)
    (q : L.sliceCarrier.carrier) (i j : Fin 3) (r : ℕ)
    (p : ℝ × EuclideanSpace ℝ (Fin 3))
    (hp : p ∈ I ×ˢ (extChartAt (𝓡 3) q).target)
    (hx : (extChartAt (𝓡 3) q).symm p.2 ∈ U) :
    iteratedFDerivWithin ℝ r (blowupPullbackCoefficient e q i j)
        (I ×ˢ (extChartAt (𝓡 3) q).target) p =
      iteratedFDerivWithin ℝ r
        (fixedCylinderMetricCoefficient F L.sliceCarrier a Q
          (fun y => (e.forward s hs y).val) q i j)
        (I ×ˢ (extChartAt (𝓡 3) q).target) p := by
  have hcont : ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin 3) =>
      (extChartAt (𝓡 3) q).symm p.2) p :=
    (continuousAt_extChartAt_symm'' hp.2).comp continuousAt_snd
  have hnear := hcont.preimage_mem_nhds (hU.mem_nhds hx)
  have heq : blowupPullbackCoefficient e q i j =ᶠ[
      𝓝[I ×ˢ (extChartAt (𝓡 3) q).target] p]
      fixedCylinderMetricCoefficient F L.sliceCarrier a Q
        (fun y => (e.forward s hs y).val) q i j := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hnear] with z hz hzU
    exact cylinder_coefficient_eq_fixed F e hI hU hs q i j z hz.1 hzU
  exact heq.iteratedFDerivWithin_eq
    (cylinder_coefficient_eq_fixed F e hI hU hs q i j p hp.1 hx) r




theorem blowupSequence_fixed_metric_CInfinity (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    {J : Set ℝ} (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR) J)
    (q : L.limit.sliceCarrier.carrier) (j r : ℕ)
    (K : Set (ℝ × EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K)
    (hKU : K ⊆ {p | p ∈ blowupMetricChartDomain L.limit q ∧
      (extChartAt (𝓡 3) q).symm p.2 ∈ L.exhaustion.space j})
    (eta : ℝ) (heta : 0 < eta) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N,
      K ⊆ Icc (-L.exhaustion.time k) 0 ×ˢ (extChartAt (𝓡 3) q).target ∧
      ∀ a b : Fin 3, ∀ p ∈ K,
        ‖iteratedFDerivWithin ℝ r
            (fixedCylinderMetricCoefficient E.flow.base.flow L.limit.sliceCarrier
              (t (L.subsequence k)) ((blowupSequence P E t x ht hR).scale (L.subsequence k))
              (fun y => ((L.embedding k).forward 0
                ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ y).val) q a b)
            (Icc (-L.exhaustion.time k) 0 ×ˢ (extChartAt (𝓡 3) q).target) p -
          iteratedFDerivWithin ℝ r
            (FlowCarrier.coordinateCoefficient L.limit.carrier q
              (fun t x v w => (L.limit.flow.metric t).inner x v w) a b)
            (blowupMetricChartDomain L.limit q) p‖ < eta := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  obtain ⟨N, hjN, hN⟩ := L.pullback_metric_CInfinity q j r K hK hKU eta heta
  refine ⟨N, hjN, ?_⟩
  intro k hk
  refine ⟨(hN k hk).1, ?_⟩
  intro a b p hp
  have hsource := L.exhaustion.space_increasing (hjN.trans hk) (hKU hp).2
  have hjet := cylinder_coefficient_jet_eq_fixed E.flow.base.flow (L.embedding k)
    isPreconnected_Icc (L.exhaustion.space_open k)
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ q a b r p
    ((hN k hk).1 hp) hsource
  exact (congrArg (fun A => ‖A - iteratedFDerivWithin ℝ r
    (FlowCarrier.coordinateCoefficient L.limit.carrier q
      (fun t x v w => (L.limit.flow.metric t).inner x v w) a b)
    (blowupMetricChartDomain L.limit q) p‖) hjet).symm.trans_lt ((hN k hk).2 a b p hp)

end PoincareConjecture.M35.OrdinaryRealization
