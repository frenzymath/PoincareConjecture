import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Restart.Flow.Extension
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Flow.Canonical


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Surgery.TerminalRestart



def strongNeckOfEvent {A : SurgeryFlowData.{u}} {U : ℝ}
    {hU : U ∈ A.surgery_times} [Nonempty (A.slice U).carrier]
    (K : SurgeryEventData A.standard_initial A.local_constants A.parameters A.slice A.metric U)
    (heq : K = A.event U hU) (i : Fin K.cap_count)
    (cylinder : SurgeryFlowCylinder A K.terminal U ((K.necks i).neck.scale⁻¹ ^ 2)
      (Ioo (-1 : ℝ) 0) (K.necks i).neck.carrier)
    (href : ∀ s hs, ∀ ht : U + s / (K.necks i).neck.scale⁻¹ ^ 2 ∈ Ico K.tMinus U,
      ∀ x ∈ (K.necks i).neck.carrier,
        cylinder.forward s hs x = K.pre_identify
          ⟨U + s / (K.necks i).neck.scale⁻¹ ^ 2, ht⟩ (K.limit_identify.inverse x))
    (hcomp : RoundCylinderFamilyClose (A.parameters.delta U) (Ioc (-1 : ℝ) 0)
      (fun s => if s = 0 then fun z v w => (K.necks i).neck.scale⁻¹ ^ 2 *
        roundCylinderPullback K.limit_metric (K.necks i).neck.coordinate_map z v w
      else surgeryCylinderPullback cylinder (K.necks i).neck.coordinate_map s)) :
    SurgeryTerminalStrongNeck A U hU (Fin.cast (congrArg (fun K => K.cap_count) heq) i) := by
  subst K
  exact ⟨cylinder, href, hcomp⟩

variable {F : SurgeryFlowData.{u}} {T : ℝ} (I : RepairedContinuationInput F T)
  (C : GeneralizedSliceCarrier.{u}) {B : ℝ≥0∞}
  (R : RicciFlow 3 C.carrier {t : ℝ | T ≤ t ∧ ENNReal.ofReal t < B})
  (E : SurgeryEventData F.standard_initial F.local_constants F.parameters
    (Splice.slice F T C R) (Splice.metric F T C R) T)
  [Nonempty C.carrier] (hC : IsCompact (univ : Set C.carrier))
  (hRP : SurgeryNoTwoSidedProjectivePlane C) (hB : ENNReal.ofReal T < B)
  (hblow : B ≠ ⊤ → ∀ L s : ℝ, s < B.toReal →
    ∃ t ∈ Ioo (max T s) B.toReal, ∃ x : C.carrier,
      L < (R.connection t).curvatureTensorNorm x)
  (hE : ∀ a b hab hJ hfree, ∀ s t : ℝ, ∀ hs : s ∈ Icc a b, ∀ ht : t ∈ Icc a b,
    ∀ hs' : s ∈ Ico E.tMinus T, ∀ ht' : t ∈ Ico E.tMinus T, ∀ x,
      (Splice.regularSlab F T C R I.time_domain_eq hab hJ hfree).transport
        ⟨s, hs⟩ ⟨t, ht⟩ (E.pre_identify ⟨s, hs'⟩ x) = E.pre_identify ⟨t, ht'⟩ x)

theorem old_strong_boundaries (U : ℝ) (hU : U ∈ F.surgery_times)
    (hU' : U ∈ (flow I C R E hC hRP hB hblow hE).surgery_times)
    [Nonempty ((flow I C R E hC hRP hB hblow hE).slice U).carrier] :
    ∀ i, Nonempty (SurgeryTerminalStrongNeck (flow I C R E hC hRP hB hblow hE) U hU' i) := by
  let := I.slices_nonempty U (F.surgery_times_subset hU)
  let A := extension I C R E hC hRP hB hblow hE
  have hUT : U < T := (I.time_domain_eq ▸ F.surgery_times_subset hU).2
  let K := Splice.oldEvent F T C R U hU hUT
  have hK : K = (flow I C R E hC hRP hB hblow hE).event U hU' :=
    (event_old I C R E U hU hU').symm
  have hcount := congrArg (fun K => K.cap_count) hK
  intro j
  let i : Fin (F.event U hU).cap_count := Fin.cast hcount.symm j
  obtain ⟨N⟩ := I.admissible.strong_boundaries U hU i
  have hN : Nonempty (SurgeryTerminalStrongNeck (flow I C R E hC hRP hB hblow hE)
      U hU' (Fin.cast hcount i)) := by
    refine ⟨strongNeckOfEvent (A := flow I C R E hC hRP hB hblow hE)
      (U := U) (hU := hU') K hK i (A.pushCylinder N.cylinder) ?_ ?_⟩
    · intro s hs ht x hx
      have hident := Splice.oldEvent_pre_identify F T C R U hU hUT
        ⟨_, ht⟩ ((F.event U hU).limit_identify.inverse x)
      have hinverse := Splice.oldEvent_limit_inverse F T C R U hU hUT x
      exact (congrArg (A.identify _ (N.cylinder.time_subset ⟨s, hs, rfl⟩))
        (N.reference_compatibility s hs ht x hx)).trans
          (hident.symm.trans (congrArg (K.pre_identify ⟨_, ht⟩) hinverse.symm))
    · apply RoundCylinderFamilyClose.congr (B' := fun s => if s = 0 then
          fun z v w => ((F.event U hU).necks i).neck.scale⁻¹ ^ 2 *
            roundCylinderPullback (F.event U hU).limit_metric
              ((F.event U hU).necks i).neck.coordinate_map z v w
        else surgeryCylinderPullback N.cylinder ((F.event U hU).necks i).neck.coordinate_map s)
        ?_ N.comparison
      intro s hs z hz v w
      by_cases hzero : s = 0
      · simp only [if_pos hzero]
        rfl
      · have hsi : s ∈ Ioo (-1 : ℝ) 0 := ⟨hs.1, lt_of_le_of_ne hs.2 hzero⟩
        have hz' : z.2 ∈ Ioo (-((F.event U hU).necks i).neck.epsilon⁻¹)
            ((F.event U hU).necks i).neck.epsilon⁻¹ := by
          simpa only [(F.event U hU).neck_delta i] using hz
        have hcoord := ((F.event U hU).necks i).neck.coordinate_map_eq (z.1, ⟨z.2, hz'⟩)
        have hmem : ((F.event U hU).necks i).neck.coordinate_map z ∈
            ((F.event U hU).necks i).neck.carrier :=
          hcoord ▸ (((F.event U hU).necks i).neck.coordinate (z.1, ⟨z.2, hz'⟩)).property
        simp only [if_neg hzero, surgeryCylinderPullback, dif_pos hsi]
        exact A.pushCylinder_pullbackInner N.cylinder ((F.event U hU).necks i).neck.carrier_open
          s hsi (((F.event U hU).necks i).neck.coordinate_map z) hmem _ _
  simpa only [i, Fin.cast_cast, Fin.cast_refl, id_eq] using hN

end PoincareConjecture.Surgery.TerminalRestart
