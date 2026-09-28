import PoincareConjecture.Proofs.M47.LimitCanonicalComponentCertificate
import PoincareConjecture.Proofs.M47.LimitCanonicalComponentScaling
import PoincareConjecture.Proofs.M47.BlowupControlsComponent










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




theorem limitCanonical_eventually_component_control
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (G : GeneralizedBlowupConvergence V (blowupBackwardInterval ⊤))
    (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    {kappa C : ℝ} (hkappa : 0 < kappa)
    (hnc : BlowupLimitNoncollapsed G.limit kappa) (hC : C ≤ S.setup.C) :
    letI : ConnectedSpace G.limit.sliceCarrier.carrier := G.limit.connectedSpace
    let K : AncientKappaSolution 3 G.limit.sliceCarrier.carrier :=
      (limitAncientIdentification P.m04 G.limit kappa hkappa hnc).certificate.solution
    ∀ _N : M27CanonicalComponent K 0 C,
      ∀ᶠ k in atTop,
        ∃ ht : (V.base (G.subsequence k)).1 ∈ (V.flow (G.subsequence k)).interval,
          SurgeryCanonicalControl (F (G.subsequence k))
            (V.base (G.subsequence k)).1
            ((R (G.subsequence k)).forward _ ht (V.base (G.subsequence k)).2)
            S.setup.epsilon S.setup.C := by
  let : ConnectedSpace G.limit.sliceCarrier.carrier := G.limit.connectedSpace
  dsimp only
  intro N
  filter_upwards [limitCanonical_component_eventually_certificate G P F R hkappa hnc N]
    with k hk
  obtain ⟨Nphys, _hcarrier, hx⟩ := hk
  let f := limitCanonicalPhysicalTerminalChart G F R k
  let Nraw := limitCanonical_component_unscale
    ((F (G.subsequence k)).connection
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
    (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k)) Nphys
  have hcanon : SurgeryCanonicalControl (F (G.subsequence k))
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k))
      (f G.limit.base) S.setup.epsilon S.setup.C :=
    SurgeryCanonicalControl.component (component_relax_constant Nraw hC) hx
  have hzero : 0 ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  have ht : (V.base (G.subsequence k)).1 ∈ (V.flow (G.subsequence k)).interval := by
    simpa only [zero_div, add_zero] using limitCanonical_terminal_clock_mem G k
  have hbase : (G.embedding k).pointMap 0 hzero G.limit.base = V.base (G.subsequence k) := by
    simpa only [GeneralizedFlowCylinder.pointMap, zero_div, add_zero] using
      G.base_preserving k hzero
  have hpoint := limitCanonicalPhysicalChart_point_identity (G.embedding k)
    (G.exhaustion.space_open k) (R (G.subsequence k)) 0 hzero
    (limitCanonical_terminal_clock_mem G k) G.limit.base
    (V.base (G.subsequence k)) ht hbase
  have hprop := congrArg
    (fun p : (t : ℝ) × ((F (G.subsequence k)).slice t).carrier =>
      SurgeryCanonicalControl (F (G.subsequence k)) p.1 p.2 S.setup.epsilon S.setup.C) hpoint
  exact ⟨ht, hprop.mp hcanon⟩

end PoincareConjecture.M47
