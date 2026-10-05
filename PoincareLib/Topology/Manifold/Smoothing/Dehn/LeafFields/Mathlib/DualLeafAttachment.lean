import PoincareLib.Topology.Manifold.Smoothing.Dehn.Regions.Mathlib.DualBlockUnionBoundary
import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.SurfaceDualEdgeGeometry
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.SurfaceVertexDualDisk
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.FinitePLDiskAttachment

/-!
# Attaching an actual leaf block with its complete outer rim

A vertex having one neighbor in the retained full vertex set meets that
union in one complete dual interval. Both interval endpoints lie in the
remaining blocks, and no other interval point does. The checked planar
attachment therefore constructs the enlarged disk with its whole outer
mark. See Putman, Theorem 5.1, pp. 15--16, and M76 Dehn derivation 021,
section 5.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E) [Fintype K.faces]

private theorem face_of_mem_vertex_dualBlocks {p q x : E}
    (hp : x ∈ (K.barycentricDualBlock {p}).space)
    (hq : x ∈ (K.barycentricDualBlock {q}).space) : ({p, q} : Finset E) ∈ K.faces := by
  by_contra h
  have hx := (K.vertex_dualBlocks_space_inter p q).subset ⟨hp, hq⟩
  rw [K.barycentricDualBlock_space_eq_empty_of_not_face (Finset.insert_nonempty p {q}) h]
    at hx
  exact hx

/-- A block with exactly one original neighbor in a retained vertex set
meets its entire union in precisely that neighbor edge's whole dual block.
See Dehn derivation 021, section 5. -/
theorem vertexDualUnion_inter_leaf_block
    {S : Set K.vertices} {p q : K.vertices} (hq : q ∈ S)
    (hleaf : ∀ r ∈ S, ({p.val, r.val} : Finset E) ∈ K.faces → r = q) :
    K.vertexDualUnion S ∩ (K.barycentricDualBlock {p.val}).space =
      (K.barycentricDualBlock {p.val, q.val}).space := by
  classical
  apply Subset.antisymm
  · intro x hx
    obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hx.1
    have he := hleaf r hr (K.face_of_mem_vertex_dualBlocks hx.2 hxr)
    subst r
    exact (K.vertex_dualBlocks_space_inter p.val q.val).subset ⟨hx.2, hxr⟩
  · intro x hx
    have hpair := (K.vertex_dualBlocks_space_inter p.val q.val).symm.subset hx
    exact ⟨mem_iUnion₂.mpr ⟨q, hq, hpair.2⟩, hpair.1⟩

variable [FiniteDimensional ℝ E]

/-- The actual leaf attachment constructs a PL disk on the enlarged union,
retaining the entire complementary-block interface as its rim. All interval
and endpoint geometry is derived from the original surface and unique leaf
neighbor; only the preceding smaller disk is the induction hypothesis.
See Dehn derivation 021, section 5. -/
theorem isFinitePLBallPair_vertexDualUnion_insert_of_leaf
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    {S : Set K.vertices} {p q : K.vertices} (hp : p ∉ S) (hq : q ∈ S)
    (hedge : ({p.val, q.val} : Finset E) ∈ K.faces)
    (hleaf : ∀ r ∈ S, ({p.val, r.val} : Finset E) ∈ K.faces → r = q)
    (hS : IsFinitePLBallPair (ℝ × ℝ) (K.vertexDualUnion S) (K.vertexDualRim S)) :
    IsFinitePLBallPair (ℝ × ℝ) (K.vertexDualUnion (insert p S))
      (K.vertexDualRim (insert p S)) := by
  classical
  have hpq : p.val ≠ q.val := by
    intro h
    have he : p = q := Subtype.ext h
    exact hp (he.symm ▸ hq)
  have hbound (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ 3 := by
    obtain ⟨t, _, ht, hst⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq ht
  obtain ⟨t, _, u, _, _, _, _, _, hcent, hI, _, hcontact⟩ :=
    K.exists_surface_dual_edge_interval hbound hcofaces hpq hedge
  have hinter := K.vertexDualUnion_inter_leaf_block hq hleaf
  have hpI := K.dualEdge_space_subset_vertex_links p.property q.property hpq
  have hIold : (K.barycentricDualBlock {p.val, q.val}).space ⊆ K.vertexDualRim S := by
    intro x hx
    have hpair := hinter.symm.subset hx
    exact ⟨hpair.1, mem_iUnion₂.mpr ⟨p, hp, hpair.2⟩⟩
  have hInew : (K.barycentricDualBlock {p.val, q.val}).space ⊆
      (K.barycentricSubdivision.link p.val).space := fun _ hx => (hpI hx).1
  have hremain : (K.barycentricDualBlock {p.val, q.val}).space ∩
        K.vertexDualUnion (insert p S)ᶜ = {t.centroid ℝ id, u.centroid ℝ id} := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hx.2
      have hrv : r.val ∈ K.vertices \ ({p.val, q.val} : Set E) := by
        refine ⟨r.property, ?_⟩
        rintro (h | h)
        · exact hr (Or.inl (Subtype.ext h))
        · have he : r = q := Subtype.ext h
          exact hr (Or.inr (he.symm ▸ hq))
      exact hcontact.subset ⟨hx.1, mem_iUnion₂.mpr ⟨r.val, hrv, hxr⟩⟩
    · intro x hx
      have hwhole := hcontact.symm.subset hx
      obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hwhole.2
      let rK : K.vertices := ⟨r, hr.1⟩
      have hrout : rK ∉ insert p S := by
        rintro (hrp | hrS)
        · exact hr.2 (Or.inl (congrArg Subtype.val hrp))
        · have hxp := (K.vertex_dualBlocks_space_inter p.val q.val).symm.subset hwhole.1
          have he := hleaf rK hrS (K.face_of_mem_vertex_dualBlocks hxp.1 hxr)
          exact hr.2 (Or.inr (congrArg Subtype.val he))
      exact ⟨hwhole.1, mem_iUnion₂.mpr ⟨rK, hrout, hxr⟩⟩
  have hpDisk := K.isFinitePLBallPair_barycentricDualBlock_vertex
    hpure hcofaces p.property (hlinks p.val p.property)
  have hglue := hS.union_of_boundary_interval hpDisk hI hIold hInew hcent hinter
  have hcarrier : K.vertexDualUnion (insert p S) =
      K.vertexDualUnion S ∪ (K.barycentricDualBlock {p.val}).space := by
    rw [K.vertexDualUnion_insert, union_comm]
  rw [hcarrier, K.vertexDualRim_insert_of_contact hp hinter hremain]
  exact hglue

end Geometry.SimplicialComplex
