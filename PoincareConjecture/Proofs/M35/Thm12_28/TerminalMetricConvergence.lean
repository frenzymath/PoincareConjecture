import PoincareConjecture.Proofs.M35.Thm12_28.FixedMetricSmoothness
import Mathlib.Analysis.Calculus.TangentCone.Real









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization




theorem blowupSequence_terminal_spatial_CInfinity (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    (q : L.limit.sliceCarrier.carrier) (j r : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K)
    (hKU : K ⊆ {p | p ∈ (extChartAt (𝓡 3) q).target ∧
      (extChartAt (𝓡 3) q).symm p ∈ L.exhaustion.space j})
    (eta : ℝ) (heta : 0 < eta) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N, ∀ a b : Fin 3, ∀ p ∈ K,
      ‖iteratedFDeriv ℝ r (fun z =>
          fixedCylinderMetricCoefficient E.flow.base.flow L.limit.sliceCarrier
            (t (L.subsequence k)) ((blowupSequence P E t x ht hR).scale (L.subsequence k))
            (fun y => ((L.embedding k).forward 0
              ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ y).val) q a b (0, z)) p -
        iteratedFDeriv ℝ r (fun z => FlowCarrier.coordinateCoefficient L.limit.carrier q
          (fun s y v w => (L.limit.flow.metric s).inner y v w) a b (0, z)) p‖ < eta := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have hJ : UniqueDiffOn ℝ (blowupBackwardInterval ⊤) := by
    convert uniqueDiffOn_Iic (0 : ℝ) using 1
    ext s
    simp [blowupBackwardInterval]
  have hKprod : IsCompact (({0} : Set ℝ) ×ˢ K) := isCompact_singleton.prod hK
  have hsource : ({0} : Set ℝ) ×ˢ K ⊆ {p | p ∈ blowupMetricChartDomain L.limit q ∧
      (extChartAt (𝓡 3) q).symm p.2 ∈ L.exhaustion.space j} := by
    intro p hp
    have hpzero : p.1 = 0 := hp.1
    exact ⟨⟨hpzero.symm ▸ L.limit.zero_mem, (hKU hp.2).1⟩, (hKU hp.2).2⟩
  obtain ⟨N, hjN, hN⟩ := blowupSequence_fixed_metric_CInfinity P E t x ht hR L q j r
    (({0} : Set ℝ) ×ˢ K) hKprod hsource eta heta
  refine ⟨N, hjN, ?_⟩
  intro k hk a b p hp
  let I := Icc (-L.exhaustion.time k) 0
  have hzero : (0 : ℝ) ∈ I := ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
  let f : L.limit.sliceCarrier.carrier → StandardCapSpace :=
    fun y => ((L.embedding k).forward 0 hzero y).val
  have htime : MapsTo
      (fun s : ℝ => t (L.subsequence k) +
        s / (blowupSequence P E t x ht hR).scale (L.subsequence k)) I
      (Ico 0 E.flow.base.lifetime) :=
    fun s hs => ((L.embedding k).forward s hs L.limit.base).property
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (L.exhaustion.space k) :=
    (sliceDiffeomorph (htime hzero)).contMDiff.comp_contMDiffOn
      ((L.embedding k).forward_smooth 0 hzero)
  have hspatial := fixedCylinderMetricCoefficient_spatialJet E.flow.base.flow
    L.limit.sliceCarrier (t (L.subsequence k))
    ((blowupSequence P E t x ht hR).scale (L.subsequence k)) f q a b
    (L.exhaustion.space_open k) hf
    (uniqueDiffOn_Icc (neg_neg_of_pos (L.exhaustion.time_pos k))) hzero htime
    (hKU hp).1 (L.exhaustion.space_increasing (hjN.trans hk) (hKU hp).2) r
  have hlimitsmooth := metricFamily_contDiffOn_spacetime_chartCoefficient
    L.limit.flow.smooth q a b
  have hlimit := iteratedFDeriv_zero_slice_of_contDiffOn hJ L.limit.zero_mem
    (isOpen_extChartAt_target (I := 𝓡 3) q) hlimitsmooth (hKU hp).1 r
  change iteratedFDeriv ℝ r
      (fun z => FlowCarrier.coordinateCoefficient L.limit.carrier q
        (fun s y v w => (L.limit.flow.metric s).inner y v w) a b (0, z)) p = _ at hlimit
  rw [hspatial, hlimit]
  let B := iteratedFDerivWithin ℝ r
    (fixedCylinderMetricCoefficient E.flow.base.flow L.limit.sliceCarrier
      (t (L.subsequence k)) ((blowupSequence P E t x ht hR).scale (L.subsequence k))
      f q a b) (I ×ˢ (extChartAt (𝓡 3) q).target) (0, p) -
    iteratedFDerivWithin ℝ r
      (FlowCarrier.coordinateCoefficient L.limit.carrier q
        (fun s y v w => (L.limit.flow.metric s).inner y v w) a b)
      (blowupMetricChartDomain L.limit q) (0, p)
  change ‖B.compContinuousLinearMap
    (fun _ => ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3)))‖ < eta
  have hnorm : ‖B.compContinuousLinearMap
      (fun _ => ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3)))‖ ≤ ‖B‖ :=
    (B.norm_compContinuousLinearMap_le _).trans
      ((mul_le_mul_of_nonneg_left (Finset.prod_le_one
        (fun _ _ => norm_nonneg _) (fun _ _ =>
          ContinuousLinearMap.norm_inr_le_one ℝ ℝ (EuclideanSpace ℝ (Fin 3))))
        (norm_nonneg B)).trans_eq (mul_one _))
  exact hnorm.trans_lt ((hN k hk).2 a b (0, p) ⟨rfl, hp⟩)

end PoincareConjecture.M35.OrdinaryRealization
