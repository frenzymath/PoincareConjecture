import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Neck.Curvature.NeckAxialDerivative

/-!
# Compact inner slabs of the actual neck

Morgan-Tian Definition 2.16, p. 30, and Theorem 12.28, pp. 323-324.
The actual patch and inverse identities identify the open inner slab,
its compact closed extension, and the axial value at every exit point.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.StandardCylinderPatch

variable {length : ℝ} {center : StandardCapSpace}

/-- Definition 2.16, p. 30: a closed axial slab strictly inside the
supplied coordinate interval lies in the actual open neck carrier. -/
theorem closed_axial_slab_subset_carrier (N : StandardCylinderPatch length center)
    {a : ℝ} (ha : a < length) :
    N.coordinate '' (univ ×ˢ Icc (-a) a) ⊆ N.carrier := by
  rintro _ ⟨z, hz, rfl⟩
  rw [← N.coordinate_image]
  exact ⟨z, ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩, rfl⟩

/-- Definition 2.16, p. 30: the closed inner axial slab is compact
under the actual spatial coordinate supplied by the neck certificate. -/
theorem compact_axial_slab (N : StandardCylinderPatch length center)
    {a : ℝ} (ha : a < length) :
    IsCompact (N.coordinate '' (univ ×ˢ Icc (-a) a)) := by
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply N.coordinate_smooth.continuousOn.mono
  intro z hz
  exact ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩

/-- Definition 2.16, p. 30: the inner open slab is open in the actual
target manifold, using the supplied continuous inverse on its carrier. -/
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

/-- Definition 2.16, p. 30: a point in the closed slab outside its
open interior has absolute actual axial coordinate equal to the half-length. -/
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

end PoincareMT.StandardCylinderPatch
