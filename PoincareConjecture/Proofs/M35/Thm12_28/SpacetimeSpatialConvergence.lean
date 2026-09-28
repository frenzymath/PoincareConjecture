import PoincareConjecture.Proofs.M35.Thm12_28.FixedMetricSmoothness
import Mathlib.Analysis.Calculus.TangentCone.Real

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

theorem blowupSequence_spacetime_spatial_CInfinity (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
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
        ‖iteratedFDeriv ℝ r (fun z =>
            fixedCylinderMetricCoefficient E.flow.base.flow L.limit.sliceCarrier
              (t (L.subsequence k)) ((blowupSequence P E t x ht hR).scale (L.subsequence k))
              (fun y => ((L.embedding k).forward 0
                ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ y).val)
              q a b (p.1, z)) p.2 -
          iteratedFDeriv ℝ r (fun z => FlowCarrier.coordinateCoefficient L.limit.carrier q
            (fun s y v w => (L.limit.flow.metric s).inner y v w) a b (p.1, z)) p.2‖ < eta := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have hJ : UniqueDiffOn ℝ (blowupBackwardInterval ⊤) := by
    convert uniqueDiffOn_Iic (0 : ℝ) using 1
    ext s
    simp [blowupBackwardInterval]
  obtain ⟨N, hjN, hN⟩ := blowupSequence_fixed_metric_CInfinity P E t x ht hR L q j r
    K hK hKU eta heta
  refine ⟨N, hjN, fun k hk => ⟨(hN k hk).1, ?_⟩⟩
  intro a b p hp
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
  have hspatial := fixedCylinderMetricCoefficient_spatialJetAt E.flow.base.flow
    L.limit.sliceCarrier (t (L.subsequence k))
    ((blowupSequence P E t x ht hR).scale (L.subsequence k)) f q a b
    (L.exhaustion.space_open k) hf
    (uniqueDiffOn_Icc (neg_neg_of_pos (L.exhaustion.time_pos k))) ((hN k hk).1 hp).1 htime
    (hKU hp).1.2 (L.exhaustion.space_increasing (hjN.trans hk) (hKU hp).2) r
  have hlimitsmooth := metricFamily_contDiffOn_spacetime_chartCoefficient
    L.limit.flow.smooth q a b
  have hlimit := iteratedFDeriv_time_slice_of_contDiffOn hJ (hKU hp).1.1
    (isOpen_extChartAt_target (I := 𝓡 3) q) hlimitsmooth (hKU hp).1.2 r
  change iteratedFDeriv ℝ r
      (fun z => FlowCarrier.coordinateCoefficient L.limit.carrier q
        (fun s y v w => (L.limit.flow.metric s).inner y v w) a b (p.1, z)) p.2 = _ at hlimit
  rw [hspatial, hlimit]
  let B := iteratedFDerivWithin ℝ r
    (fixedCylinderMetricCoefficient E.flow.base.flow L.limit.sliceCarrier
      (t (L.subsequence k)) ((blowupSequence P E t x ht hR).scale (L.subsequence k))
      f q a b) (I ×ˢ (extChartAt (𝓡 3) q).target) p -
    iteratedFDerivWithin ℝ r
      (FlowCarrier.coordinateCoefficient L.limit.carrier q
        (fun s y v w => (L.limit.flow.metric s).inner y v w) a b)
      (blowupMetricChartDomain L.limit q) p
  change ‖B.compContinuousLinearMap
    (fun _ => ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3)))‖ < eta
  have hnorm : ‖B.compContinuousLinearMap
      (fun _ => ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3)))‖ ≤ ‖B‖ :=
    (B.norm_compContinuousLinearMap_le _).trans
      ((mul_le_mul_of_nonneg_left (Finset.prod_le_one
        (fun _ _ => norm_nonneg _) (fun _ _ =>
          ContinuousLinearMap.norm_inr_le_one ℝ ℝ (EuclideanSpace ℝ (Fin 3))))
        (norm_nonneg B)).trans_eq (mul_one _))
  exact hnorm.trans_lt ((hN k hk).2 a b p hp)

theorem blowupSequence_spatial_jet_tendsto_moving (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    (q : L.limit.sliceCarrier.carrier) (j r : ℕ) (a b : Fin 3)
    (K : Set (ℝ × EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K)
    (hKU : K ⊆ {p | p ∈ blowupMetricChartDomain L.limit q ∧
      (extChartAt (𝓡 3) q).symm p.2 ∈ L.exhaustion.space j})
    (sigma : ℕ → ℕ) (hsigma : Tendsto sigma atTop atTop)
    (pseq : ℕ → ℝ × EuclideanSpace ℝ (Fin 3)) (hpseq : ∀ k, pseq k ∈ K)
    (p : ℝ × EuclideanSpace ℝ (Fin 3)) (hp : p ∈ K)
    (hplim : Tendsto pseq atTop (𝓝 p)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    Tendsto (fun k => iteratedFDeriv ℝ r (fun z =>
        fixedCylinderMetricCoefficient E.flow.base.flow L.limit.sliceCarrier
          (t (L.subsequence (sigma k)))
          ((blowupSequence P E t x ht hR).scale (L.subsequence (sigma k)))
          (fun y => ((L.embedding (sigma k)).forward 0
            ⟨neg_nonpos.mpr (L.exhaustion.time_pos (sigma k)).le, le_rfl⟩ y).val)
          q a b ((pseq k).1, z)) (pseq k).2) atTop
      (𝓝 (iteratedFDeriv ℝ r (fun z => FlowCarrier.coordinateCoefficient L.limit.carrier q
        (fun s y v w => (L.limit.flow.metric s).inner y v w) a b (p.1, z)) p.2)) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  let F (k : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin 3)) :=
    iteratedFDeriv ℝ r (fun z =>
      fixedCylinderMetricCoefficient E.flow.base.flow L.limit.sliceCarrier
        (t (L.subsequence k)) ((blowupSequence P E t x ht hR).scale (L.subsequence k))
        (fun y => ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ y).val) q a b (p.1, z)) p.2
  let G (p : ℝ × EuclideanSpace ℝ (Fin 3)) :=
    iteratedFDeriv ℝ r (fun z => FlowCarrier.coordinateCoefficient L.limit.carrier q
      (fun s y v w => (L.limit.flow.metric s).inner y v w) a b (p.1, z)) p.2
  have hJ : UniqueDiffOn ℝ (blowupBackwardInterval ⊤) := by
    convert uniqueDiffOn_Iic (0 : ℝ) using 1
    ext s
    simp [blowupBackwardInterval]
  have hG : ContinuousOn G (blowupMetricChartDomain L.limit q) :=
    continuousOn_spatial_jet_of_contDiffOn hJ
      (isOpen_extChartAt_target (I := 𝓡 3) q)
      (metricFamily_contDiffOn_spacetime_chartCoefficient L.limit.flow.smooth q a b) r
  have hlimit : Tendsto (fun k => G (pseq k)) atTop (𝓝 (G p)) :=
    (hG p (hKU hp).1).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hplim, Eventually.of_forall (fun k => (hKU (hpseq k)).1)⟩)
  have hdiff : Tendsto (fun k => F (sigma k) (pseq k) - G (pseq k)) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro eta heta
    obtain ⟨N, _, hN⟩ := blowupSequence_spacetime_spatial_CInfinity
      P E t x ht hR L q j r K hK hKU eta heta
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hsigma.eventually (eventually_ge_atTop N))
    refine ⟨k₀, fun k hk => ?_⟩
    simpa only [dist_zero_right] using (hN (sigma k) (hk₀ k hk)).2 a b (pseq k) (hpseq k)
  have hsum := hdiff.add hlimit
  simpa only [sub_add_cancel, zero_add] using hsum

theorem blowupSequence_spatial_error_jets (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    (q : L.limit.sliceCarrier.carrier) (j : ℕ) (a b : Fin 3)
    (K : Set (ℝ × EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K)
    (hKU : K ⊆ {p | p ∈ blowupMetricChartDomain L.limit q ∧
      (extChartAt (𝓡 3) q).symm p.2 ∈ L.exhaustion.space j})
    (sigma : ℕ → ℕ) (hsigma : Tendsto sigma atTop atTop)
    (pseq : ℕ → ℝ × EuclideanSpace ℝ (Fin 3)) (hpseq : ∀ k, pseq k ∈ K) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    let A (k : ℕ) (y : EuclideanSpace ℝ (Fin 3)) :=
      fixedCylinderMetricCoefficient E.flow.base.flow L.limit.sliceCarrier
        (t (L.subsequence (sigma k)))
        ((blowupSequence P E t x ht hR).scale (L.subsequence (sigma k)))
        (fun z => ((L.embedding (sigma k)).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos (sigma k)).le, le_rfl⟩ z).val)
        q a b ((pseq k).1, y) -
      FlowCarrier.coordinateCoefficient L.limit.carrier q
        (fun s z v w => (L.limit.flow.metric s).inner z v w) a b ((pseq k).1, y)
    (∀ᶠ k in atTop, ContDiffAt ℝ ∞ (A k) (pseq k).2) ∧
      ∀ r : ℕ, Tendsto (fun k => iteratedFDeriv ℝ r (A k) (pseq k).2) atTop (𝓝 0) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  let f (k : ℕ) (z : L.limit.sliceCarrier.carrier) := ((L.embedding k).forward 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
  let B (k : ℕ) (y : EuclideanSpace ℝ (Fin 3)) :=
    fixedCylinderMetricCoefficient E.flow.base.flow L.limit.sliceCarrier
      (t (L.subsequence (sigma k)))
      ((blowupSequence P E t x ht hR).scale (L.subsequence (sigma k)))
      (f (sigma k)) q a b ((pseq k).1, y)
  let C (k : ℕ) (y : EuclideanSpace ℝ (Fin 3)) :=
    FlowCarrier.coordinateCoefficient L.limit.carrier q
      (fun s z v w => (L.limit.flow.metric s).inner z v w) a b ((pseq k).1, y)
  have hreg : ∀ᶠ k in atTop,
      ContDiffAt ℝ ∞ (B k) (pseq k).2 ∧ ContDiffAt ℝ ∞ (C k) (pseq k).2 := by
    filter_upwards [hsigma.eventually (eventually_ge_atTop j)] with k hk
    have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time (sigma k)) 0 :=
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos (sigma k)).le, le_rfl⟩
    have htime : t (L.subsequence (sigma k)) +
        0 / (blowupSequence P E t x ht hR).scale (L.subsequence (sigma k)) ∈
          Ico 0 E.flow.base.lifetime :=
      ((L.embedding (sigma k)).forward 0 hzero L.limit.base).property
    have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f (sigma k)) (L.exhaustion.space (sigma k)) :=
      (sliceDiffeomorph htime).contMDiff.comp_contMDiffOn
        ((L.embedding (sigma k)).forward_smooth 0 hzero)
    refine ⟨fixedCylinderMetricCoefficient_contDiffAt_spatial E.flow.base.flow
      L.limit.sliceCarrier _ _ (f (sigma k)) q a b (L.exhaustion.space_open _) hf
      (pseq k).1 (pseq k).2 (hKU (hpseq k)).1.2
      (L.exhaustion.space_increasing hk (hKU (hpseq k)).2), ?_⟩
    have hc := ((L.limit.flow.metric (pseq k).1).contDiffOn_chartCoefficients q).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds (hKU (hpseq k)).1.2)
    exact (hc.clm_apply (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 3) ℝ a))).clm_apply
      (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 3) ℝ b))
  refine ⟨hreg.mono (fun _ hk => hk.1.sub hk.2), fun r => ?_⟩
  have herr : Tendsto (fun k => iteratedFDeriv ℝ r (B k) (pseq k).2 -
      iteratedFDeriv ℝ r (C k) (pseq k).2) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro eta heta
    obtain ⟨N, _, hN⟩ := blowupSequence_spacetime_spatial_CInfinity
      P E t x ht hR L q j r K hK hKU eta heta
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hsigma.eventually (eventually_ge_atTop N))
    refine ⟨k₀, fun k hk => ?_⟩
    simpa only [dist_zero_right] using (hN (sigma k) (hk₀ k hk)).2 a b (pseq k) (hpseq k)
  apply herr.congr'
  filter_upwards [hreg] with k hk
  have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
  exact (fun_iteratedFDeriv_sub_apply (hk.1.of_le hr) (hk.2.of_le hr)).symm

end PoincareConjecture.M35.OrdinaryRealization
