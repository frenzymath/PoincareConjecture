import PoincareConjecture.Proofs.M11.IntervalMaps
import PoincareConjecture.Definitions.M11GeneralizedFlow





set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}

abbrev boxDomain (b : AdaptedMetricBox n X time I) :=
  (smoothInterval b.interval).Point × b.spatial

theorem boxDomain_nonempty (b : AdaptedMetricBox n X time I) : Nonempty (boxDomain b) := by
  obtain ⟨t, ht⟩ := b.interval.nontrivial.nonempty
  obtain ⟨x, hx⟩ := b.spatial_nonempty
  exact ⟨(⟨t, ht⟩, ⟨x, hx⟩)⟩

noncomputable def boxHomeomorph (b : AdaptedMetricBox n X time I) :
    OpenPartialHomeomorph (boxDomain b) X := by
  letI := boxDomain_nonempty b
  exact b.openEmbedding.toOpenPartialHomeomorph b.toSpacetime

theorem boxHomeomorph_apply (b : AdaptedMetricBox n X time I) (p : boxDomain b) :
    boxHomeomorph b p = b.toSpacetime p := rfl

theorem boxHomeomorph_source (b : AdaptedMetricBox n X time I) :
    (boxHomeomorph b).source = univ := rfl

theorem boxHomeomorph_target (b : AdaptedMetricBox n X time I) :
    (boxHomeomorph b).target = range b.toSpacetime := by
  simp [boxHomeomorph]

theorem boxHomeomorph_left_inv (b : AdaptedMetricBox n X time I) (p : boxDomain b) :
    (boxHomeomorph b).symm (b.toSpacetime p) = p :=
  (boxHomeomorph b).left_inv (mem_univ p)

theorem boxHomeomorph_right_inv (b : AdaptedMetricBox n X time I)
    {p : X} (hp : p ∈ (boxHomeomorph b).target) :
    b.toSpacetime ((boxHomeomorph b).symm p) = p :=
  (boxHomeomorph b).right_inv hp

theorem boxHomeomorph_inverse_time (b : AdaptedMetricBox n X time I)
    {p : X} (hp : p ∈ (boxHomeomorph b).target) :
    ((boxHomeomorph b).symm p).1.val = time p := by
  rw [← b.time_toSpacetime, boxHomeomorph_right_inv b hp]


theorem box_transition_eventually_eq (b c : AdaptedMetricBox n X time I)
    (p : boxDomain b) {y : EuclideanSpace ℝ (Fin n)}
    (T : AdaptedMetricTransition b c p.1.val p.2.val y) :
    ∀ᶠ q in 𝓝 p,
      ((boxHomeomorph c).symm (b.toSpacetime q)).1.val = q.1.val ∧
      ((boxHomeomorph c).symm (b.toSpacetime q)).2.val = T.coordinateChange q.2.val := by
  obtain ⟨U, hU, hTU⟩ := T.interval_relatively_open
  have htU : p.1.val ∈ U := by
    have ht := T.time_mem
    rw [hTU] at ht
    exact ht.2
  filter_upwards [
    (hU.preimage (continuous_subtype_val.comp continuous_fst)).mem_nhds htU,
    (T.coordinateChange.open_source.preimage
      (continuous_subtype_val.comp continuous_snd)).mem_nhds T.source_mem] with q hqt hqx
  have ht : q.1.val ∈ T.interval.domain := by
    rw [hTU]
    exact ⟨b.interval_subset q.1.property, hqt⟩
  have heq := T.box_eq q.1.val ht q.2.val hqx
  change b.toSpacetime q = c.toSpacetime
    (⟨q.1.val, T.interval_subset_right ht⟩,
      ⟨T.coordinateChange q.2.val, T.target_subset (T.coordinateChange.map_source hqx)⟩)
    at heq
  rw [heq, boxHomeomorph_left_inv]
  exact ⟨rfl, rfl⟩

theorem box_transition_data (A : AdaptedMetricAtlas n X) (b c : A.box_index)
    (p : boxDomain (A.box b))
    (hp : (A.box b).toSpacetime p ∈ (boxHomeomorph (A.box c)).target) :
    Nonempty (AdaptedMetricTransition (A.box b) (A.box c) p.1.val p.2.val
      ((boxHomeomorph (A.box c)).symm ((A.box b).toSpacetime p)).2.val) := by
  let q := (boxHomeomorph (A.box c)).symm ((A.box b).toSpacetime p)
  have ht : q.1.val = p.1.val :=
    (boxHomeomorph_inverse_time (A.box c) hp).trans ((A.box b).time_toSpacetime p)
  have hc : p.1.val ∈ (A.box c).interval.domain := ht ▸ q.1.property
  apply A.transitions b c p.1.val p.1.property hc p.2 q.2
  have hq : (⟨p.1.val, hc⟩, q.2) = q := by
    apply Prod.ext
    · exact Subtype.ext ht.symm
    · rfl
  rw [hq]
  exact (boxHomeomorph_right_inv (A.box c) hp).symm

end PoincareConjecture.Proofs.M11
