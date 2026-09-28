import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Splice
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Flow.Geometry

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Surgery.TerminalRestart

variable {F : SurgeryFlowData.{u}} {T : ℝ} (I : RepairedContinuationInput F T)
  (C : GeneralizedSliceCarrier.{u}) {B : ℝ≥0∞}
  (R : RicciFlow 3 C.carrier {t : ℝ | T ≤ t ∧ ENNReal.ofReal t < B})

include I

theorem slices_nonempty [Nonempty C.carrier] (t : ℝ) (ht : 0 ≤ t) :
    Nonempty (Splice.slice F T C R t).carrier := by
  by_cases h : t < T
  · obtain ⟨x⟩ := I.slices_nonempty t (I.time_domain_eq ▸ (show t ∈ Ico 0 T from ⟨ht, h⟩))
    exact ⟨Splice.identifyBefore F T C R t h x⟩
  · obtain ⟨x⟩ := (inferInstance : Nonempty C.carrier)
    exact ⟨Splice.identifyAfter F T C R t (le_of_not_gt h) x⟩

theorem slices_compact (hC : IsCompact (univ : Set C.carrier))
    (t : ℝ) (ht : 0 ≤ t) : IsCompact (univ : Set (Splice.slice F T C R t).carrier) := by
  by_cases h : t < T
  · exact SurgeryEventRebuild.relabel
      (C := fun p => IsCompact (univ : Set p.1.carrier))
      (Splice.family_before F T C R h).symm
      (F.slices_compact t (I.time_domain_eq ▸ (show t ∈ Ico 0 T from ⟨ht, h⟩)))
  · exact SurgeryEventRebuild.relabel
      (C := fun p => IsCompact (univ : Set p.1.carrier))
      (Splice.family_after F T C R (le_of_not_gt h)).symm hC

theorem no_two_sided_projective_plane (hC : SurgeryNoTwoSidedProjectivePlane C)
    (t : ℝ) (ht : 0 ≤ t) : SurgeryNoTwoSidedProjectivePlane (Splice.slice F T C R t) := by
  by_cases h : t < T
  · simpa only [Splice.slice, Splice.family, if_pos h] using
      F.no_two_sided_projective_plane t
        (I.time_domain_eq ▸ (show t ∈ Ico 0 T from ⟨ht, h⟩))
  · simpa only [Splice.slice, Splice.family, if_neg h] using hC

theorem initial_normalized : ∀ x : (Splice.slice F T C R 0).carrier,
    (Splice.connection F T C R 0).curvatureTensorNorm x ≤ 1 ∧
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        ENNReal.ofReal (euclideanUnitBallLebesgueVolume.toReal * r ^ 3 / 2) ≤
          calibratedMetricVolume (Splice.metric F T C R 0)
            ((Splice.metric F T C R 0).ball x r) := by
  have hcopy (p q : SurgeryEventRebuild.SliceMetric.{u}) (h : p = q)
      (D : LeviCivitaData p.2)
      (hD : ∀ x : p.1.carrier, D.curvatureTensorNorm x ≤ 1 ∧
        ∀ r : ℝ, 0 < r → r ≤ 1 →
          ENNReal.ofReal (euclideanUnitBallLebesgueVolume.toReal * r ^ 3 / 2) ≤
            calibratedMetricVolume p.2 (p.2.ball x r)) :
      ∀ x : q.1.carrier,
        (SurgeryEventRebuild.relabel (C := fun z => LeviCivitaData z.2) h D).curvatureTensorNorm x ≤ 1 ∧
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            ENNReal.ofReal (euclideanUnitBallLebesgueVolume.toReal * r ^ 3 / 2) ≤
              calibratedMetricVolume q.2 (q.2.ball x r) := by
    subst q
    exact hD
  unfold Splice.connection
  rw [dif_pos I.terminal_pos]
  exact hcopy ⟨F.slice 0, F.metric 0⟩ _
    (Splice.family_before F T C R I.terminal_pos).symm (F.connection 0) F.initial_normalized

theorem old_times (hB : ENNReal.ofReal T < B) :
    F.time_domain ⊆ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < B} := by
  intro t ht
  have h := I.time_domain_eq ▸ ht
  exact ⟨h.1, (ENNReal.ofReal_le_ofReal h.2.le).trans_lt hB⟩

theorem no_later_event (t : ℝ) (ht : T < t) : t ∉ Splice.eventTimes F T := by
  rintro (h | h)
  · exact ht.ne' h
  · exact (ht.trans (I.time_domain_eq ▸ F.surgery_times_subset h).2).false

end PoincareConjecture.Surgery.TerminalRestart
