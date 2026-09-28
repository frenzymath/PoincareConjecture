import PoincareConjecture.Proofs.Horizon.Compat.M33SphereNonempty
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.EmptyTail
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Splice.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.RegularHistory









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Surgery.Extinction

variable {F : SurgeryFlowData.{u}} {T : ℝ} (I : RepairedContinuationInput F T)

def connection (t : ℝ) : LeviCivitaData (metric F T t) :=
  Splice.connection F T (emptyCarrier (F.slice 0)) (emptyFlow (F.metric 0) T) t

include I

theorem slices_compact (t : ℝ) (ht : 0 ≤ t) : IsCompact (univ : Set (slice F T t).carrier) := by
  by_cases h : t < T
  · have htF : t ∈ F.time_domain := I.time_domain_eq ▸ (show t ∈ Ico 0 T from ⟨ht, h⟩)
    exact SurgeryEventRebuild.relabel
      (C := fun p => IsCompact (univ : Set p.1.carrier))
      (Splice.family_before F T (emptyCarrier (F.slice 0)) (emptyFlow (F.metric 0) T) h).symm
      (F.slices_compact t htF)
  · let := slice_empty_after F T (le_of_not_gt h)
    exact isCompact_univ

theorem no_two_sided_projective_plane (t : ℝ) (ht : 0 ≤ t) :
    SurgeryNoTwoSidedProjectivePlane (slice F T t) := by
  by_cases h : t < T
  · have htF : t ∈ F.time_domain := I.time_domain_eq ▸ (show t ∈ Ico 0 T from ⟨ht, h⟩)
    simpa only [slice, Splice.slice, Splice.family, if_pos h] using
      F.no_two_sided_projective_plane t htF
  · let := slice_empty_after F T (le_of_not_gt h)
    rintro ⟨f, _⟩
    exact isEmptyElim (f (Quotient.mk realProjectiveTwoSetoid (Classical.arbitrary UnitTwoSphere), ⟨0, by norm_num⟩))

theorem initial_nonempty : Nonempty (slice F T 0).carrier := by
  obtain ⟨x⟩ := F.initial_nonempty
  exact ⟨Splice.identifyBefore F T (emptyCarrier (F.slice 0))
    (emptyFlow (F.metric 0) T) 0 I.terminal_pos x⟩

theorem initial_normalized : ∀ x : (slice F T 0).carrier,
    (connection (F := F) (T := T) 0).curvatureTensorNorm x ≤ 1 ∧
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        ENNReal.ofReal (euclideanUnitBallLebesgueVolume.toReal * r ^ 3 / 2) ≤
          calibratedMetricVolume (metric F T 0) ((metric F T 0).ball x r) := by
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
  unfold connection Splice.connection
  rw [dif_pos I.terminal_pos]
  exact hcopy ⟨F.slice 0, F.metric 0⟩ _
    (Splice.family_before F T (emptyCarrier (F.slice 0))
      (emptyFlow (F.metric 0) T) I.terminal_pos).symm (F.connection 0) F.initial_normalized

theorem surgery_times_finite : F.surgery_times.Finite := by
  apply I.last_slab.initial_events_finite.subset
  intro t ht
  exact ⟨ht, I.time_domain_eq ▸ F.surgery_times_subset ht⟩

omit I in
theorem event_time_old (U : ℝ) (hU : U ∈ Splice.eventTimes F T)
    [Nonempty (slice F T U).carrier] : U ∈ F.surgery_times := by
  rcases mem_insert_iff.mp hU with hEq | hold
  · subst U
    let := slice_empty_after F T le_rfl
    obtain ⟨x⟩ := (inferInstance : Nonempty (slice F T T).carrier)
    exact isEmptyElim x
  · exact hold

theorem vanishing_time_eq (U : ℝ) (hU : U ∈ Splice.eventTimes F T)
    [IsEmpty (slice F T U).carrier] : U = T := by
  rcases mem_insert_iff.mp hU with hEq | hold
  · exact hEq
  · have hUF := F.surgery_times_subset hold
    have hUT : U < T := (I.time_domain_eq ▸ hUF).2
    obtain ⟨x⟩ := I.slices_nonempty U hUF
    have y : (slice F T U).carrier := Splice.identifyBefore F T (emptyCarrier (F.slice 0))
      (emptyFlow (F.metric 0) T) U hUT x
    exact isEmptyElim y

end PoincareConjecture.Surgery.Extinction
