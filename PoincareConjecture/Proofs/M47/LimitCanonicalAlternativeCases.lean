import PoincareConjecture.Proofs.M47.LimitCanonicalPhysicalApplication









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47



theorem limitCanonical_ancient_alternative_cases
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
        ((∃ N : StrongEvolvingNeck K 0 S.setup.epsilon,
            N.center = G.limit.base) ∨
          (∃ _N : M27CanonicalCap K 0 G.limit.base S.setup.epsilon
              S.calibration.Ckappa, True) ∨
          (∃ _N : M27CanonicalComponent K 0 S.calibration.Ckappa, True) ∨
          (∃ _N : M27EpsilonRoundComponent K 0 S.setup.epsilon, True)) ∧
        S.calibration.Ckappa ≤ S.setup.C ∧
        let e := G.embedding k
        let chart := limitCanonicalPhysicalChart e (G.exhaustion.space_open k)
          (R (G.subsequence k)) 0 hzero
            (by simpa only [zero_div, add_zero] using ht)
        chart.source = G.exhaustion.space k ∧
          chart.target = limitRP2PhysicalMap e (R (G.subsequence k)) 0 hzero
              (by simpa only [zero_div, add_zero] using ht) ''
            G.exhaustion.space k
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
  have ht0 : (V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k) ∈
      (V.flow (G.subsequence k)).interval := by
    simpa only [zero_div, add_zero] using ht
  have halt := limitCanonical_ancient_alternative h04 S G F R hkappa hnc
  dsimp only [K] at halt ⊢
  obtain ⟨hcanon, hC⟩ := halt
  refine ⟨hzero, ht, ?_, hC, ?_⟩
  · rcases hcanon with ⟨hneck, hcenter⟩ | hcap | hcomponent | hround
    · exact Or.inl ⟨hneck, hcenter⟩
    · exact Or.inr (Or.inl ⟨hcap, trivial⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hcomponent, trivial⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hround, trivial⟩))
  · let e := G.embedding k
    let chart := limitCanonicalPhysicalChart e (G.exhaustion.space_open k)
      (R (G.subsequence k)) 0 hzero ht0
    refine ⟨?_, ?_⟩
    · exact limitCanonicalPhysicalChart_source e (G.exhaustion.space_open k)
        (R (G.subsequence k)) 0 hzero ht0
    · exact limitCanonicalPhysicalChart_target e (G.exhaustion.space_open k)
        (R (G.subsequence k)) 0 hzero ht0

end PoincareConjecture.M47
