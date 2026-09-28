import PoincareConjecture.Proofs.M47.LimitCanonicalAlternative
import PoincareConjecture.Proofs.M47.LimitCanonicalComponentImage

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

theorem limitCanonical_ancient_physical_application
    (h04 : RicciFlowCurvatureTheory.{u})
    (S : RepairedControlledSchedulesData.{u})
    {V : GeneralizedBlowupSequence.{u}}
    (G : GeneralizedBlowupConvergence V (blowupBackwardInterval ⊤))
    (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hnc : BlowupLimitNoncollapsed G.limit kappa) (k : ℕ) :
    letI : ConnectedSpace G.limit.sliceCarrier.carrier := G.limit.connectedSpace
    let K : AncientKappaSolution 3 G.limit.sliceCarrier.carrier :=
      (limitAncientIdentification h04 G.limit kappa hkappa hnc).certificate.solution
    ∃ hzero : 0 ∈ Icc (-G.exhaustion.time k) 0,
      ∃ ht : (V.base (G.subsequence k)).1 ∈
        (V.flow (G.subsequence k)).interval,
        M27StrongCanonicalNeighborhood K 0 G.limit.base S.setup.epsilon
            S.calibration.Ckappa ∧
          S.calibration.Ckappa ≤ S.setup.C ∧
          let e := G.embedding k
          let chart := limitCanonicalPhysicalChart e (G.exhaustion.space_open k)
            (R (G.subsequence k)) 0 hzero
              (by simpa only [zero_div, add_zero] using ht)
          chart.source = G.exhaustion.space k ∧
          chart.target = limitRP2PhysicalMap e (R (G.subsequence k)) 0 hzero
              (by simpa only [zero_div, add_zero] using ht) ''
            G.exhaustion.space k ∧
          (∀ x ∈ G.exhaustion.space k, ∀ v w,
            (V.scale (G.subsequence k)) *
                ((F (G.subsequence k)).metric
                  ((V.base (G.subsequence k)).1 +
                    0 / V.scale (G.subsequence k))).inner
                  (chart x)
                  (mfderiv (𝓡 3) (𝓡 3) chart x v)
                  (mfderiv (𝓡 3) (𝓡 3) chart x w) =
              e.pullbackInner 0 hzero x v w) ∧
          (⟨(V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k),
              chart G.limit.base⟩ :
              (t : ℝ) × ((F (G.subsequence k)).slice t).carrier) =
            ⟨(V.base (G.subsequence k)).1,
              (R (G.subsequence k)).forward
                ((V.base (G.subsequence k)).1) ht
                ((V.base (G.subsequence k)).2)⟩
  := by
  let : ConnectedSpace G.limit.sliceCarrier.carrier := G.limit.connectedSpace
  let K : AncientKappaSolution 3 G.limit.sliceCarrier.carrier :=
    (limitAncientIdentification h04 G.limit kappa hkappa hnc).certificate.solution
  have hzero : 0 ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  have ht : (V.base (G.subsequence k)).1 ∈
      (V.flow (G.subsequence k)).interval :=
    ((V.flow (G.subsequence k)).slice_nonempty_iff _).mp
      ⟨by simpa only [zero_div, add_zero] using
        (G.embedding k).forward 0 hzero G.limit.base⟩
  have hbase0 : (G.embedding k).pointMap 0 hzero G.limit.base =
      V.base (G.subsequence k) := by
    simpa only [GeneralizedFlowCylinder.pointMap, zero_div, add_zero] using
      G.base_preserving k hzero
  have halt := limitCanonical_ancient_alternative h04 S G F R hkappa hnc
  have ht0 : (V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k) ∈
      (V.flow (G.subsequence k)).interval := by
    simpa only [zero_div, add_zero] using ht
  dsimp only [K] at halt ⊢
  obtain ⟨hcanon, hC⟩ := halt
  refine ⟨hzero, ht, hcanon, hC, ?_⟩
  let e := G.embedding k
  let chart := limitCanonicalPhysicalChart e (G.exhaustion.space_open k)
    (R (G.subsequence k)) 0 hzero ht0
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact limitCanonicalPhysicalChart_source e (G.exhaustion.space_open k)
      (R (G.subsequence k)) 0 hzero ht0
  · exact limitCanonicalPhysicalChart_target e (G.exhaustion.space_open k)
      (R (G.subsequence k)) 0 hzero ht0
  · intro x hx v w
    exact limitCanonicalPhysicalChart_metric e (G.exhaustion.space_open k)
      (R (G.subsequence k)) 0 hzero ht0 hx v w
  · exact limitCanonicalPhysicalChart_point_identity e (G.exhaustion.space_open k)
      (R (G.subsequence k)) 0 hzero ht0 G.limit.base
      (V.base (G.subsequence k)) ht hbase0

end PoincareConjecture.M47
