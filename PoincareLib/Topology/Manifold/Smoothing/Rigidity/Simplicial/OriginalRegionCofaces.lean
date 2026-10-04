import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.OriginalDiskRim
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Mathlib.SubcomplexCarrierNeighborhood
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Simplicial.Mathlib.CompleteCofaceDualBlock

/-!
# Whole original triangle cofaces lie in the region

The full rim mark supplies an original interior vertex on every disk
triangle. Continuity of the literal model inverse gives a relative
carrier neighborhood there, forcing all ambient cofaces into the
original region mark. See rigidity019, section2.
-/

set_option autoImplicit false

open Set Metric Geometry
open scoped Topology

namespace PoincareMT.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

/-- Each disk triangle has a vertex whose literal inverse lies in
the interior of the original region. See rigidity019, section2. -/
theorem exists_triangle_vertex_interior
    {s : Finset (T.index → ℝ × V3)} (hs : s ∈ (T.marked 2).faces)
    (hscard : s.card = 3) : ∃ p ∈ s, (T.inverse p : X) ∈ interior R := by
  have hsK := T.marked_le 2 hs
  have hsnot : s ∉ (T.marked 3).faces := by
    intro h
    have hbound := T.rim_face_card_le h
    omega
  obtain ⟨p, hps, hpQ⟩ := SimplicialComplex.exists_vertex_off_full_subcomplex
    (T.marked_le 3) (T.marked_full 3) hsK hsnot
  have hpD : p ∈ (T.marked 2).space := (T.marked 2).subset_space hs hps
  have hpK : p ∈ T.ambient.space := T.ambient.subset_space hsK hps
  have hpB : p ∉ (T.marked 1).space := by
    intro h
    exact hpQ (T.disk_boundary_inter ▸ ⟨hpD, h⟩)
  obtain ⟨hpParam, hjp⟩ := T.parameter_disk_point hpD
  have hpR : (T.inverse p : X) ∈ R := hjp ▸ T.disk_in_region hpParam
  refine ⟨p, hps, (mem_interior_iff_notMem_frontier hpR).mpr ?_⟩
  intro hpfront
  apply hpB
  rw [T.boundary_space]
  refine ⟨T.inverse p, hpfront, ?_⟩
  rw [T.inverse_eq ⟨p, hpK⟩, ← T.model_eq (T.model.symm ⟨p, hpK⟩),
    T.model.apply_symm_apply]

/-- An actual original interior point of a modeled face forces the
whole face into the region mark. See rigidity019, section2. -/
theorem face_mem_region_of_inverse_interior
    {t : Finset (T.index → ℝ × V3)} (ht : t ∈ T.ambient.faces)
    {x : T.index → ℝ × V3} (hx : x ∈ convexHull ℝ (t : Set _))
    (hxI : (T.inverse x : X) ∈ interior R) : t ∈ (T.marked 0).faces := by
  have hxK : x ∈ T.ambient.space := T.ambient.convexHull_subset_space ht hx
  have hg : ContinuousOn (fun y => (T.inverse y : X)) T.ambient.space :=
    continuous_subtype_val.comp_continuousOn T.inverse_continuous
  have hpre : (fun y => (T.inverse y : X)) ⁻¹' interior R ∈ 𝓝[T.ambient.space] x :=
    (hg x hxK).preimage_mem_nhdsWithin (isOpen_interior.mem_nhds hxI)
  apply SimplicialComplex.face_mem_subcomplex_of_carrier_nhds (T.marked_le 0) ht hx
  filter_upwards [hpre, self_mem_nhdsWithin] with y hy hyK
  exact (T.inverse_mem_region_iff hyK).mp (interior_subset hy)

/-- Every ambient coface of an actual disk triangle belongs to the
original region, including both tetrahedral cofaces. See rigidity019. -/
theorem triangle_coface_mem_region
    {s t : Finset (T.index → ℝ × V3)} (hs : s ∈ (T.marked 2).faces)
    (hscard : s.card = 3) (ht : t ∈ T.ambient.faces) (hst : s ⊆ t) :
    t ∈ (T.marked 0).faces := by
  obtain ⟨p, hps, hpI⟩ := T.exists_triangle_vertex_interior hs hscard
  exact T.face_mem_region_of_inverse_interior ht
    (subset_convexHull ℝ _ (hst hps)) hpI

open Classical in
/-- The complete ambient dual block of a disk triangle is unchanged
on passing to the original region complex. See rigidity019, section2. -/
theorem triangle_dualBlock_eq_region
    {s : Finset (T.index → ℝ × V3)} (hs : s ∈ (T.marked 2).faces)
    (hscard : s.card = 3) :
    let : Fintype T.ambient.faces := T.finite.fintype
    let : Fintype (T.marked 0).faces := (T.marked_finite 0).fintype
    (T.marked 0).barycentricDualBlock s = T.ambient.barycentricDualBlock s := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 0).faces := (T.marked_finite 0).fintype
  exact T.ambient.barycentricDualBlock_eq_of_cofaces_in_subcomplex
    (T.marked 0) (T.marked_le 0) s
    (fun t ht hst => T.triangle_coface_mem_region hs hscard ht hst)

open Classical in
/-- Every point of the whole triangle normal interval lies in the
original region mark. See rigidity019, section2. -/
theorem triangle_dualBlock_subset_region
    {s : Finset (T.index → ℝ × V3)} (hs : s ∈ (T.marked 2).faces)
    (hscard : s.card = 3) :
    let : Fintype T.ambient.faces := T.finite.fintype
    (T.ambient.barycentricDualBlock s).space ⊆ (T.marked 0).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 0).faces := (T.marked_finite 0).fintype
  change (T.ambient.barycentricDualBlock s).space ⊆ (T.marked 0).space
  rw [← T.triangle_dualBlock_eq_region hs hscard]
  exact (SimplicialComplex.space_subset_of_le ((T.marked 0).barycentricDualBlock_le s)).trans
    (T.marked 0).barycentricSubdivision_isSubdivision.space_eq.subset

end PoincareMT.M76.OriginalProperDiskTriangulation
