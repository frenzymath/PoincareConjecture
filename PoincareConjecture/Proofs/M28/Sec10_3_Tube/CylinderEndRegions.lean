import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CompactRegions

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.OpenCylinderModel

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}

theorem mem_tail_iff_m28 (T : OpenCylinderModel U) (side : Bool) {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) {x : M} :
    x ∈ T.tail side a ↔ x ∈ U ∧
      if side then a < (T.inverse x).2 else (T.inverse x).2 < a := by
  cases side
  · change x ∈ T.coordinate '' (univ ×ˢ Ioo (0 : ℝ) a) ↔
      x ∈ U ∧ (T.inverse x).2 < a
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
        ⟨mem_univ _, hz.2.1, hz.2.2.trans ha'⟩
      exact ⟨T.coordinate_mem_m28 hz'.2, by rw [T.left_inverse hz']; exact hz.2.2⟩
    · rintro ⟨hx, hh⟩
      exact ⟨T.inverse x, ⟨mem_univ _, (T.inverse_mem x hx).2.1, hh⟩,
        T.right_inverse hx⟩
  · change x ∈ T.coordinate '' (univ ×ˢ Ioo a (1 : ℝ)) ↔
      x ∈ U ∧ a < (T.inverse x).2
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
        ⟨mem_univ _, ha.trans hz.2.1, hz.2.2⟩
      exact ⟨T.coordinate_mem_m28 hz'.2, by rw [T.left_inverse hz']; exact hz.2.1⟩
    · rintro ⟨hx, hh⟩
      exact ⟨T.inverse x, ⟨mem_univ _, hh, (T.inverse_mem x hx).2.2⟩,
        T.right_inverse hx⟩

theorem tail_subset_m28 (T : OpenCylinderModel U) (side : Bool) {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) : T.tail side a ⊆ U :=
  fun _ hx => ((T.mem_tail_iff_m28 side ha ha').mp hx).1

theorem isPreconnected_tail (T : OpenCylinderModel U) (side : Bool) {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) : IsPreconnected (T.tail side a) := by
  have hs : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) _ (by norm_num)
  let : ConnectedSpace UnitTwoSphere := Subtype.connectedSpace hs
  cases side
  · apply (isPreconnected_univ.prod isPreconnected_Ioo).image
    apply T.coordinate_smooth.continuousOn.mono
    intro z hz
    exact ⟨mem_univ _, hz.2.1, hz.2.2.trans ha'⟩
  · apply (isPreconnected_univ.prod isPreconnected_Ioo).image
    apply T.coordinate_smooth.continuousOn.mono
    intro z hz
    exact ⟨mem_univ _, ha.trans hz.2.1, hz.2.2⟩

theorem tail_nonempty (T : OpenCylinderModel U) (side : Bool) {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) : (T.tail side a).Nonempty := by
  have hs : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) _ (by norm_num)
  obtain ⟨v, hv⟩ := hs.nonempty
  let q : UnitTwoSphere := ⟨v, hv⟩
  cases side
  · obtain ⟨t, ht, ht'⟩ := exists_between ha
    exact ⟨T.coordinate (q, t), ⟨(q, t), ⟨mem_univ _, ht, ht'⟩, rfl⟩⟩
  · obtain ⟨t, ht, ht'⟩ := exists_between ha'
    exact ⟨T.coordinate (q, t), ⟨(q, t), ⟨mem_univ _, ht, ht'⟩, rfl⟩⟩

theorem isCompact_middleSphere (T : OpenCylinderModel U) :
    IsCompact T.middleSphere := by
  apply (isCompact_univ.prod (isCompact_singleton (x := (1 / 2 : ℝ)))).image_of_continuousOn
  apply T.coordinate_smooth.continuousOn.mono
  rintro z ⟨_, hz⟩
  exact ⟨mem_univ _, by simpa only [mem_singleton_iff.mp hz] using
    (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num)⟩

theorem middleSphere_subset (T : OpenCylinderModel U) : T.middleSphere ⊆ U := by
  rintro x ⟨z, ⟨_, hz⟩, rfl⟩
  apply T.coordinate_mem_m28
  simpa only [mem_singleton_iff.mp hz] using
    (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num)

theorem mem_middleSphere_iff (T : OpenCylinderModel U) {x : M} (hx : x ∈ U) :
    x ∈ T.middleSphere ↔ (T.inverse x).2 = 1 / 2 := by
  constructor
  · rintro ⟨z, ⟨_, hz⟩, rfl⟩
    have hz' : z.2 ∈ Ioo (0 : ℝ) 1 := by
      simpa only [mem_singleton_iff.mp hz] using
        (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num)
    rw [T.left_inverse ⟨mem_univ _, hz'⟩]
    exact mem_singleton_iff.mp hz
  · intro hh
    exact ⟨T.inverse x, ⟨mem_univ _, hh⟩, T.right_inverse hx⟩

end PoincareConjecture.OpenCylinderModel
