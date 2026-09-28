import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Flow.Extension
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Flow.Canonical









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Surgery.Extinction

variable {F : SurgeryFlowData.{u}} {T : ℝ} (I : RepairedContinuationInput F T)
  (V : SurgeryVanishingEventData F.parameters F.slice F.metric T)
  (hV : ∀ a b hab hJ hfree, ∀ s t : ℝ, ∀ hs : s ∈ Icc a b, ∀ ht : t ∈ Icc a b,
    ∀ hs' : s ∈ Ico V.tMinus T, ∀ ht' : t ∈ Ico V.tMinus T, ∀ x,
      (F.regular_slabs a b hab hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
        (V.pre_identify ⟨s, hs'⟩ x) = V.pre_identify ⟨t, ht'⟩ x)

def strongBoundary (U : ℝ) (hU : U ∈ F.surgery_times)
    (hU' : U ∈ (flow I V hV).surgery_times) [Nonempty (F.slice U).carrier]
    [Nonempty ((flow I V hV).slice U).carrier]
    (i : Fin (F.event U hU).cap_count) (N : SurgeryTerminalStrongNeck F U hU i) :
    SurgeryTerminalStrongNeck (flow I V hV) U hU' i := by
  let E := extension I V hV
  have hUT : U < T := (I.time_domain_eq ▸ F.surgery_times_subset hU).2
  refine {
    cylinder := E.pushCylinder N.cylinder
    reference_compatibility := ?_
    comparison := ?_ }
  · intro s hs ht x hx
    have hident := Splice.oldEvent_pre_identify F T (emptyCarrier (F.slice 0))
      (emptyFlow (F.metric 0) T) U hU hUT ⟨_, ht⟩ ((F.event U hU).limit_identify.inverse x)
    have hinverse := Splice.oldEvent_limit_inverse F T (emptyCarrier (F.slice 0))
      (emptyFlow (F.metric 0) T) U hU hUT x
    exact (congrArg (E.identify _ (N.cylinder.time_subset ⟨s, hs, rfl⟩))
      (N.reference_compatibility s hs ht x hx)).trans
        (hident.symm.trans (congrArg
          ((Splice.oldEvent F T (emptyCarrier (F.slice 0)) (emptyFlow (F.metric 0) T)
            U hU hUT).pre_identify ⟨_, ht⟩) hinverse.symm))
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
      exact E.pushCylinder_pullbackInner N.cylinder ((F.event U hU).necks i).neck.carrier_open
        s hsi (((F.event U hU).necks i).neck.coordinate_map z) hmem _ _

end PoincareConjecture.Surgery.Extinction
