import PoincareConjecture.Proofs.M51.EmptyEventSlabs
import PoincareConjecture.Proofs.M51.EmptyMaximality









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.M51Empty

noncomputable def flow (F : SurgeryFlowData.{u}) {a : ℝ}
    (ha : a ∈ F.time_domain) [IsEmpty (F.slice a).carrier] : SurgeryFlowData.{u} where
  standard_initial := F.standard_initial
  local_constants := F.local_constants
  parameters := F.parameters
  time_domain := Ici 0
  time_domain_interval := ordConnected_Ici
  time_domain_nonnegative := Subset.rfl
  zero_mem := by
    change (0 : ℝ) ≤ 0
    exact le_rfl
  slice := slice F a
  metric := metric F a
  connection := connection F a
  slices_compact := fun t ht => F.slices_compact _ (representative_mem F a ha ht)
  no_two_sided_projective_plane := fun t ht =>
    F.no_two_sided_projective_plane _ (representative_mem F a ha ht)
  initial_nonempty := by
    have ha0 : 0 ≤ a := F.time_domain_nonnegative ha
    simpa only [slice, min_eq_left ha0] using F.initial_nonempty
  initial_normalized := by
    have ha0 : 0 ≤ a := F.time_domain_nonnegative ha
    change ∀ x : (F.slice (min 0 a)).carrier,
      (F.connection (min 0 a)).curvatureTensorNorm x ≤ 1 ∧
        ∀ r : ℝ, 0 < r → r ≤ 1 →
          ENNReal.ofReal (euclideanUnitBallLebesgueVolume.toReal * r ^ 3 / 2) ≤
            calibratedMetricVolume (F.metric (min 0 a)) ((F.metric (min 0 a)).ball x r)
    rw [min_eq_left ha0]
    exact F.initial_normalized
  surgery_times := F.surgery_times
  surgery_times_subset := fun _ ht => F.time_domain_nonnegative (F.surgery_times_subset ht)
  zero_not_surgery := F.zero_not_surgery
  surgery_times_locally_finite := fun _ _ =>
    ⟨1, by norm_num, (F.surgeryTimes_finite_of_empty ha).subset inter_subset_left⟩
  regular_slabs := regularSlab F ha
  slab_transport_coherent := regularSlab_coherent F ha
  event := event F ha
  vanishing_event := vanishingEvent F ha
  event_slab_compatibility := event_slab_compatibility F ha
  vanishing_slab_compatibility := vanishing_slab_compatibility F ha
  maximal_intervals := fun p q hp hstart hpq _ hfree _ hend =>
    maximality F ha p q hp hstart hpq hfree hend
  extinction_permanent := fun s t hs _ hst he => empty_forward F a ha hs hst he

variable (F : SurgeryFlowData.{u}) {a : ℝ} (ha : a ∈ F.time_domain)
    [IsEmpty (F.slice a).carrier]

@[simp] theorem flow_time_domain : (flow F ha).time_domain = Ici 0 := rfl

@[simp] theorem flow_parameters : (flow F ha).parameters = F.parameters := rfl

@[simp] theorem flow_surgery_times : (flow F ha).surgery_times = F.surgery_times := rfl

theorem flow_empty_after {t : ℝ} (ht : a ≤ t) : IsEmpty ((flow F ha).slice t).carrier :=
  empty_after F a ht

theorem flow_events_finite : (flow F ha).surgery_times.Finite :=
  F.surgeryTimes_finite_of_empty ha

end PoincareConjecture.M51Empty
