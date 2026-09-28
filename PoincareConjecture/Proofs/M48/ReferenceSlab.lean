import PoincareConjecture.Proofs.M48.RegularGuards

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RepairedPreterminalSlab

variable {F : SurgeryFlowData.{u}} {T : ℝ} (L : RepairedPreterminalSlab F T)
  {a : ℝ} (ha : L.start < a) (haT : a < T)

include ha in
theorem reference_window_subset : Ico a T ⊆ Ico L.start T :=
  fun _ ht => ⟨ha.le.trans ht.1, ht.2⟩

include ha in
theorem reference_regular (t : ℝ) (ht : t ∈ Ico a T) : t ∉ F.surgery_times :=
  fun hevent => disjoint_left.mp L.surgery_free hevent ⟨ha.trans_le ht.1, ht.2⟩

def referenceFlow : RicciFlow 3 (F.slice L.start).carrier (Ico a T) where
  metric := L.flow.metric
  connection := L.flow.connection
  interval := ordConnected_Ico
  nontrivial := by
    obtain ⟨b, hab, hbT⟩ := exists_between haT
    exact ⟨a, ⟨le_rfl, haT⟩, b, ⟨hab.le, hbT⟩, hab.ne⟩
  smooth := L.flow.smooth.mono (prod_mono (L.reference_window_subset ha) Subset.rfl)
  equation t ht x v w :=
    (L.flow.equation t (L.reference_window_subset ha ht) x v w).mono
      (L.reference_window_subset ha)

noncomputable def referenceCylinder :
    SurgeryFlowCylinder F (F.slice L.start) 0 1 (Ico a T) univ where
  scale_pos := zero_lt_one
  interval_connected := ordConnected_Ico
  time_subset := by simpa using (L.time_subset.trans' (L.reference_window_subset ha))
  forward s hs := L.identify
    ⟨0 + s / 1, by simpa only [div_one, zero_add] using L.reference_window_subset ha hs⟩
  inverse s hs := (L.identify
    ⟨0 + s / 1, by simpa only [div_one, zero_add] using L.reference_window_subset ha hs⟩).symm
  forward_smooth _ _ := Diffeomorph.contMDiff _ |>.contMDiffOn
  inverse_smooth _ _ := Diffeomorph.contMDiff _ |>.contMDiffOn
  left_inverse s hs x _ := (L.identify ⟨0 + s / 1, _⟩).left_inv x
  right_inverse s hs x _ := (L.identify ⟨0 + s / 1, _⟩).right_inv x
  slab_compatibility b c hbc hJ hS s hs t ht hs' ht' x _ :=
    L.transport_compatibility b c hbc hJ hS _ _ hs' ht' _ _ x
  retained_at_surgery s hs hS := by
    exact (L.reference_regular ha s hs (by simpa only [div_one, zero_add] using hS)).elim
  pre_retained_at_surgery s hs hS := by
    exact (L.reference_regular ha s hs (by simpa only [div_one, zero_add] using hS)).elim
  surgery_compatibility s hs hS := by
    exact (L.reference_regular ha s hs (by simpa only [div_one, zero_add] using hS)).elim

end PoincareConjecture.RepairedPreterminalSlab
