import PoincareConjecture.Proofs.M47.LimitCanonicalCapCertificate
import PoincareConjecture.Proofs.M47.LimitCanonicalAlternativeCases
import PoincareConjecture.Proofs.M47.BlowupControlsCapScaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {V : GeneralizedBlowupSequence.{u}}

private local instance (G : GeneralizedBlowupConvergence V (blowupBackwardInterval ⊤)) :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance (G : GeneralizedBlowupConvergence V (blowupBackwardInterval ⊤)) :
    ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance (G : GeneralizedBlowupConvergence V (blowupBackwardInterval ⊤)) :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold
private local instance (G : GeneralizedBlowupConvergence V (blowupBackwardInterval ⊤)) :
    MeasurableSpace G.limit.carrier.carrier := G.limit.carrier.measurableSpace
private local instance (G : GeneralizedBlowupConvergence V (blowupBackwardInterval ⊤)) :
    BorelSpace G.limit.carrier.carrier := G.limit.carrier.borelSpace
private local instance (G : GeneralizedBlowupConvergence V (blowupBackwardInterval ⊤)) :
    T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space

theorem limitCanonical_eventually_cap_control
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (G : GeneralizedBlowupConvergence V (blowupBackwardInterval ⊤))
    (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    {kappa C : ℝ} (hkappa : 0 < kappa)
    (hnc : BlowupLimitNoncollapsed G.limit kappa) (hC : C ≤ S.setup.C) :
    letI : ConnectedSpace G.limit.sliceCarrier.carrier := G.limit.connectedSpace
    let K : AncientKappaSolution 3 G.limit.sliceCarrier.carrier :=
      (limitAncientIdentification P.m04 G.limit kappa hkappa hnc).certificate.solution
    ∀ _N : M27CanonicalCap K 0 G.limit.base S.setup.epsilon C,
      ∀ᶠ k in atTop,
        ∃ ht : (V.base (G.subsequence k)).1 ∈ (V.flow (G.subsequence k)).interval,
          SurgeryCanonicalControl (F (G.subsequence k))
            (V.base (G.subsequence k)).1
            ((R (G.subsequence k)).forward _ ht (V.base (G.subsequence k)).2)
            S.setup.epsilon S.setup.C := by
  let : ConnectedSpace G.limit.sliceCarrier.carrier := G.limit.connectedSpace
  dsimp only
  intro N
  obtain ⟨H, hHe, hHC, hHD, hbase⟩ := M34.exists_normalized_limit_cap_of_ancient
    G.limit (limitAncientIdentification P.m04 G.limit kappa hkappa hnc) N
  filter_upwards [limitCanonical_eventually_cap_certificate G P F R H hHD hbase] with k hk
  obtain ⟨Nnorm, hNe, hNC, _hND, _hNcore, _hNclosed, _hNcarrier, _hNboundary,
    _hNmodel, hcenter⟩ := hk
  let f := limitCanonicalPhysicalTerminalChart G F R k
  obtain ⟨Nraw, hRe, hRC, hRD, hRcore, _hRcarrier⟩ := exists_cap_of_rescaled_metric
    ((F (G.subsequence k)).metric
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
    ((F (G.subsequence k)).connection
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
    (V.base_scalar_pos (G.subsequence k)) Nnorm
  have hcanon : SurgeryCanonicalControl (F (G.subsequence k))
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k))
      (f G.limit.base) S.setup.epsilon S.setup.C :=
    SurgeryCanonicalControl.cap Nraw (hRe.trans (hNe.trans hHe))
      ((hRC.trans hNC).trans_le (hHC.trans hC)) hRD (hRcore.symm ▸ hcenter)
  have hzero : 0 ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  have ht : (V.base (G.subsequence k)).1 ∈ (V.flow (G.subsequence k)).interval := by
    simpa only [zero_div, add_zero] using limitCanonical_terminal_clock_mem G k
  have hbasepoint : (G.embedding k).pointMap 0 hzero G.limit.base =
      V.base (G.subsequence k) := by
    simpa only [GeneralizedFlowCylinder.pointMap, zero_div, add_zero] using
      G.base_preserving k hzero
  have hpoint := limitCanonicalPhysicalChart_point_identity (G.embedding k)
    (G.exhaustion.space_open k) (R (G.subsequence k)) 0 hzero
    (limitCanonical_terminal_clock_mem G k) G.limit.base
    (V.base (G.subsequence k)) ht hbasepoint
  have hprop := congrArg
    (fun p : (t : ℝ) × ((F (G.subsequence k)).slice t).carrier =>
      SurgeryCanonicalControl (F (G.subsequence k)) p.1 p.2 S.setup.epsilon S.setup.C) hpoint
  exact ⟨ht, hprop.mp hcanon⟩

end PoincareConjecture.M47
