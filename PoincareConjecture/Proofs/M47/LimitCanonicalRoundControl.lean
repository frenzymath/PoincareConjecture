import PoincareConjecture.Proofs.M47.LimitCanonicalRoundCertificate
import PoincareConjecture.Proofs.M47.LimitCanonicalAlternative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option linter.style.haveILetI false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {V : GeneralizedBlowupSequence.{u}}

private local instance (G : GeneralizedBlowupConvergence V (blowupBackwardInterval ⊤)) :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance (G : GeneralizedBlowupConvergence V (blowupBackwardInterval ⊤)) :
    ChartedSpace E3 G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance (G : GeneralizedBlowupConvergence V (blowupBackwardInterval ⊤)) :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

theorem limitCanonical_eventually_round_control
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (G : GeneralizedBlowupConvergence V (blowupBackwardInterval ⊤))
    (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hnc : BlowupLimitNoncollapsed G.limit kappa) :
    letI : ConnectedSpace G.limit.sliceCarrier.carrier := G.limit.connectedSpace
    let K : AncientKappaSolution 3 G.limit.sliceCarrier.carrier :=
      (limitAncientIdentification P.m04 G.limit kappa hkappa hnc).certificate.solution
    ∀ _N : M27EpsilonRoundComponent K 0 S.setup.epsilon,
      ∀ᶠ k in atTop,
        ∃ ht : (V.base (G.subsequence k)).1 ∈ (V.flow (G.subsequence k)).interval,
          SurgeryCanonicalControl (F (G.subsequence k))
            (V.base (G.subsequence k)).1
            ((R (G.subsequence k)).forward _ ht (V.base (G.subsequence k)).2)
            S.setup.epsilon S.setup.C := by
  letI : ConnectedSpace G.limit.sliceCarrier.carrier := G.limit.connectedSpace
  dsimp only
  intro N
  letI : TopologicalSpace N.reference := N.reference_topology
  letI : ChartedSpace E3 N.reference := N.reference_charted
  letI : IsManifold (𝓡 3) ∞ N.reference := N.reference_manifold
  letI : CompactSpace N.reference := isCompact_univ_iff.mp N.reference_compact
  let C : CovariantTensorEvaluation 3 N.reference 2 :=
    fun y v => N.scale * (G.limit.flow.metric 0).inner (N.identification y)
      (mfderiv (𝓡 3) (𝓡 3) N.identification y (v 0))
      (mfderiv (𝓡 3) (𝓡 3) N.identification y (v 1))
  have hC : IsSmoothCovariantTensor C :=
    (M44.isSmoothCovariantTensor_metric_pullback
      (G.limit.flow.metric 0) N.identification.contMDiff).const_mul N.scale
  have hold : ∃ b : ℝ, b < S.setup.epsilon ^ 2 ∧ ∀ x : N.reference,
      singularMetricJetErrorSquared N.reference_metric N.reference_connection C
        (Nat.floor S.setup.epsilon⁻¹) x ≤ b := by
    obtain ⟨b, hb, hbound⟩ := N.comparison
    refine ⟨b, hb, ?_⟩
    intro x
    rw [limitCanonical_singularMetricJetErrorSquared_eq N.reference_connection hC]
    exact hbound x
  obtain ⟨bound, hbound, hcompare⟩ := limitCanonical_round_comparison_bound P G N.compact
    N.reference_metric N.reference_connection N.identification.contMDiff
    N.scale (Nat.floor S.setup.epsilon⁻¹) hold
  filter_upwards [hcompare, limitCanonical_eventually_exhaustion_univ G N.compact]
    with k hk hfull
  have hzero : 0 ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  have ht : (V.base (G.subsequence k)).1 ∈ (V.flow (G.subsequence k)).interval :=
    ((V.flow (G.subsequence k)).slice_nonempty_iff _).mp
      ⟨by simpa only [zero_div, add_zero] using
        (G.embedding k).forward 0 hzero G.limit.base⟩
  have ht0 : (V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k) ∈
      (V.flow (G.subsequence k)).interval := by
    simpa only [zero_div, add_zero] using ht
  let f := limitCanonicalPhysicalChart (G.embedding k) (G.exhaustion.space_open k)
    (R (G.subsequence k)) 0 hzero ht0
  have hsource : f.source = univ :=
    (limitCanonicalPhysicalChart_source (G.embedding k) (G.exhaustion.space_open k)
      (R (G.subsequence k)) 0 hzero ht0).trans hfull
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f :=
    contMDiffOn_univ.mp (hsource ▸ f.contMDiffOn_toFun)
  have htensor : limitCanonicalRoundSourceTensor (G.embedding k) N.identification 0 hzero
      N.scale = (fun y v => (N.scale * V.scale (G.subsequence k)) *
        singularMetricPullback
          ((F (G.subsequence k)).metric
            ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
          (f ∘ N.identification) y v) := by
    funext y v
    unfold limitCanonicalRoundSourceTensor singularMetricPullback
    rw [mfderiv_comp y (hf.mdifferentiableAt (by simp))
      (N.identification.contMDiff.mdifferentiableAt (by simp))]
    rw [mul_assoc]
    exact congrArg (N.scale * ·)
      (limitCanonicalPhysicalChart_metric (G.embedding k) (G.exhaustion.space_open k)
        (R (G.subsequence k)) 0 hzero ht0 (hfull ▸ mem_univ (N.identification y))
        (mfderiv (𝓡 3) (𝓡 3) N.identification y (v 0))
        (mfderiv (𝓡 3) (𝓡 3) N.identification y (v 1))).symm
  let Nphys := limitCanonical_round_image N
    ((F (G.subsequence k)).metric
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
    f hsource G.limit.base (V.scale (G.subsequence k))
    (V.base_scalar_pos (G.subsequence k)) ⟨bound, hbound, fun x => by
      rw [← htensor]
      exact hk x⟩
  have hcanon : SurgeryCanonicalControl (F (G.subsequence k))
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k))
      (f G.limit.base) S.setup.epsilon S.setup.C :=
    SurgeryCanonicalControl.round Nphys (f.map_source (hsource ▸ mem_univ G.limit.base))
  have hbase : (G.embedding k).pointMap 0 hzero G.limit.base = V.base (G.subsequence k) := by
    simpa only [GeneralizedFlowCylinder.pointMap, zero_div, add_zero] using
      G.base_preserving k hzero
  have hpoint := limitCanonicalPhysicalChart_point_identity (G.embedding k)
    (G.exhaustion.space_open k) (R (G.subsequence k)) 0 hzero ht0 G.limit.base
    (V.base (G.subsequence k)) ht hbase
  have hprop := congrArg
    (fun p : (t : ℝ) × ((F (G.subsequence k)).slice t).carrier =>
      SurgeryCanonicalControl (F (G.subsequence k)) p.1 p.2 S.setup.epsilon S.setup.C) hpoint
  exact ⟨ht, hprop.mp hcanon⟩

end PoincareConjecture.M47
