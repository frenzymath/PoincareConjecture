import PoincareConjecture.Proofs.M51.EmptyTerminalNeck
import PoincareConjecture.Proofs.M48.ExtensionCanonical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M51Empty

variable (F : SurgeryFlowData.{u}) {a : ℝ} (ha : a ∈ F.time_domain)
    [IsEmpty (F.slice a).carrier]

theorem admissible (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (h : SurgeryFlowAdmissible F) : SurgeryFlowAdmissible (flow F ha) := by
  constructor
  · intro T hT hNew i
    change T ∈ F.surgery_times at hT
    let : Nonempty (F.slice T).carrier := by
      simpa only [flow, slice, event_clock F ha T hT T le_rfl] using hNew
    rcases h.strong_boundaries T hT i with ⟨N⟩
    exact ⟨terminalStrongNeck F ha T hT i N⟩
  · intro T hT hNew t hstart x hx
    change T ∈ F.surgery_times at hT
    let : Nonempty (F.slice T).carrier := by
      simpa only [flow, slice, event_clock F ha T hT T le_rfl] using hNew
    let E := F.event T hT
    let c := M51EventCopy.identify F.slice (fun s => min s a) E.tMinus
      (event_clock F ha T hT _ E.tMinus_lt.le)
    have hnot : c.symm x ∉ interior E.retained_pre := by
      intro hxold
      apply hx
      have himage := E.reindexPast_retained_pre_image
        (fun s => min s a) (event_clock F ha T hT)
      change x ∈ interior (E.reindexPast (fun s => min s a)
        (event_clock F ha T hT)).retained_pre
      rw [← himage]
      change x ∈ interior (c.toHomeomorph '' E.retained_pre)
      rw [← c.toHomeomorph.image_interior]
      exact ⟨c.symm x, hxold, c.apply_symm_apply x⟩
    have htold : t.1 ∈ F.time_domain :=
      F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT)
        ⟨E.tMinus_nonnegative.trans t.2.1, t.2.2.le⟩
    have hold := (extension F ha).canonical_control m13 t.1 htold
      (E.pre_identify t (c.symm x)) F.parameters.epsilon F.parameters.C
      (h.strong_disappearing T hT t hstart (c.symm x) hnot)
    have hmap : (extension F ha).identify t.1 htold (E.pre_identify t (c.symm x)) =
        ((flow F ha).event T hT).pre_identify t x := by
      change identify F ha t.1 htold _ = _
      rw [identify_of_le F ha _ _ (t.2.2.le.trans (F.surgeryTime_le_empty ha hT))]
      change M51EventCopy.identify F.slice (fun s => min s a) t.1
        (event_clock F ha T hT _ t.2.2.le) (E.pre_identify t (c.symm x)) =
          (E.reindexPast (fun s => min s a) (event_clock F ha T hT)).pre_identify t x
      have hm := E.reindexPast_pre_identify_apply
        (fun s => min s a) (event_clock F ha T hT) t (c.symm x)
      simpa only [c, Diffeomorph.apply_symm_apply] using hm.symm
    rw [hmap] at hold
    exact hold
  · intro T hT hNew t hstart x
    change T ∈ F.surgery_times at hT
    let : IsEmpty (F.slice T).carrier := by
      simpa only [flow, slice, event_clock F ha T hT T le_rfl] using hNew
    let E := F.vanishing_event T hT
    let c := M51EventCopy.identify F.slice (fun s => min s a) E.tMinus
      (event_clock F ha T hT _ E.tMinus_lt.le)
    have htold : t.1 ∈ F.time_domain :=
      F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT)
        ⟨E.tMinus_nonnegative.trans t.2.1, t.2.2.le⟩
    have hold := (extension F ha).canonical_control m13 t.1 htold
      (E.pre_identify t (c.symm x)) F.parameters.epsilon F.parameters.C
      (h.strong_vanishing T hT t hstart (c.symm x))
    have hmap : (extension F ha).identify t.1 htold (E.pre_identify t (c.symm x)) =
        ((flow F ha).vanishing_event T hT).pre_identify t x := by
      change identify F ha t.1 htold _ = _
      rw [identify_of_le F ha _ _ (t.2.2.le.trans (F.surgeryTime_le_empty ha hT))]
      change M51EventCopy.identify F.slice (fun s => min s a) t.1
        (event_clock F ha T hT _ t.2.2.le) (E.pre_identify t (c.symm x)) =
          (E.reindexPast (fun s => min s a) (event_clock F ha T hT)).pre_identify t x
      have hm := E.reindexPast_pre_identify_apply
        (fun s => min s a) (event_clock F ha T hT) t (c.symm x)
      simpa only [c, Diffeomorph.apply_symm_apply] using hm.symm
    rw [hmap] at hold
    exact hold

end PoincareConjecture.M51Empty
