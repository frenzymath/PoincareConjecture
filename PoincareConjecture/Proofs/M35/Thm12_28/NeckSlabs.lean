import PoincareConjecture.Proofs.M35.Thm12_28.NeckAxialDerivative









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.StandardCylinderPatch

variable {length : ℝ} {center : StandardCapSpace}



theorem closed_axial_slab_subset_carrier (N : StandardCylinderPatch length center)
    {a : ℝ} (ha : a < length) :
    N.coordinate '' (univ ×ˢ Icc (-a) a) ⊆ N.carrier := by
  rintro _ ⟨z, hz, rfl⟩
  rw [← N.coordinate_image]
  exact ⟨z, ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩, rfl⟩



theorem compact_axial_slab (N : StandardCylinderPatch length center)
    {a : ℝ} (ha : a < length) :
    IsCompact (N.coordinate '' (univ ×ˢ Icc (-a) a)) := by
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply N.coordinate_smooth.continuousOn.mono
  intro z hz
  exact ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩



theorem open_axial_slab (N : StandardCylinderPatch length center)
    {a : ℝ} (ha : a ≤ length) :
    IsOpen (N.coordinate '' (univ ×ˢ Ioo (-a) a)) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hz, rfl⟩
  have hdom : z ∈ univ ×ˢ Ioo (-length) length :=
    ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hmem : N.coordinate z ∈ N.carrier :=
    N.coordinate_image ▸ mem_image_of_mem N.coordinate hdom
  have hinv := N.coordinate_left_inverse hdom
  have hax : (N.inverse (N.coordinate z)).2 ∈ Ioo (-a) a := by
    simpa only [hinv] using hz.2
  have hcont := (N.axial_contMDiffAt hmem).continuousAt
  filter_upwards [N.carrier_open.mem_nhds hmem,
    hcont.preimage_mem_nhds (isOpen_Ioo.mem_nhds hax)] with y hy hiy
  exact ⟨N.inverse y, ⟨mem_univ _, hiy⟩, N.coordinate_right_inverse hy⟩



theorem axial_abs_eq_at_slab_exit (N : StandardCylinderPatch length center)
    {a : ℝ} (ha : a < length) {y : StandardCapSpace}
    (hy : y ∈ N.coordinate '' (univ ×ˢ Icc (-a) a))
    (hout : y ∉ N.coordinate '' (univ ×ˢ Ioo (-a) a)) :
    |(N.inverse y).2| = a := by
  obtain ⟨z, hz, rfl⟩ := hy
  have hdom : z ∈ univ ×ˢ Ioo (-length) length :=
    ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  rw [N.coordinate_left_inverse hdom]
  apply le_antisymm (abs_le.mpr ⟨by linarith [hz.2.1], hz.2.2⟩)
  by_contra h
  have habs : |z.2| < a := lt_of_not_ge h
  have hzopen : z ∈ univ ×ˢ Ioo (-a) a := ⟨mem_univ _, abs_lt.mp habs⟩
  exact hout ⟨z, hzopen, rfl⟩

end PoincareConjecture.StandardCylinderPatch
