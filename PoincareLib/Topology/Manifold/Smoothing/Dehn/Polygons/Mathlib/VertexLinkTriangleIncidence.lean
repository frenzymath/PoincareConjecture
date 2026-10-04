import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.LinkGraphIncidence
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.FaceLinkCofaceCount

/-!
# Actual triangles and edge cofaces of a vertex link

Adjoining and erasing the original central vertex retain the complete
face sets. Iterated links identify the exact coface counts. See Dehn
derivation 016 and Hatcher, Algebraic Topology, pp. 235--239.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E)

/-- Every face in the full original vertex link lies in an actual
triangle, by erasing the central vertex from a tetrahedral coface.
See Dehn derivation 016. -/
theorem faceLink_singleton_triangular_pure
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) (p : E) :
    ∀ s ∈ (K.faceLink {p}).faces,
      ∃ t ∈ (K.faceLink {p}).faces, s ⊆ t ∧ t.card = 3 := by
  intro s hs
  obtain ⟨t, ht, hst, htc⟩ := hpure _ hs.2.2
  have hpt : p ∈ t := hst (Finset.mem_union_left _ (Finset.mem_singleton_self p))
  have hcard : (t.erase p).card = 3 := by
    rw [Finset.card_erase_of_mem hpt, htc]
  have hne : (t.erase p).Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨t.erase p, ⟨K.down_closed ht (Finset.erase_subset _ _) hne,
    Finset.disjoint_singleton_left.mpr (Finset.notMem_erase _ _), ?_⟩, ?_, hcard⟩
  · simpa only [Finset.singleton_union, Finset.insert_erase hpt] using ht
  · intro v hv
    exact Finset.mem_erase.mpr
      ⟨fun hvp => Finset.disjoint_singleton_left.mp hs.2.1 (hvp ▸ hv),
        hst (Finset.mem_union_right _ hv)⟩

/-- The triangles above an actual link edge are counted by the
original joined triangle's complete link. See Dehn derivation 016. -/
theorem vertexLink_triangle_cofaces_ncard
    {p : E} {e : Finset E} (he : e ∈ (K.faceLink {p}).faces) (hec : e.card = 2) :
    {t : Finset E | t ∈ (K.faceLink {p}).faces ∧ t.card = 3 ∧ e ⊆ t}.ncard =
      (K.faceLink (insert p e)).vertices.ncard := by
  have hcount := (K.faceLink {p}).ncard_faceLink_vertices_eq_cofaces e
  rw [K.faceLink_faceLink _ _ he.2.1, Finset.singleton_union] at hcount
  simpa only [hec, Nat.reduceAdd] using hcount.symm

/-- A central vertex outside the original subcomplex cannot occur
in any of its joined faces. See Dehn derivation 016. -/
theorem insert_notMem_faces_of_vertex_off_subcomplex
    (A : SimplicialComplex ℝ E) {p : E} (hp : p ∉ A.vertices) (e : Finset E) :
    insert p e ∉ A.faces := by
  intro h
  exact hp (A.down_closed h (Finset.singleton_subset_iff.mpr
    (Finset.mem_insert_self p e)) (Finset.singleton_nonempty p))

/-- An original boundary triangle at p supplies an actual link edge
whose join lies in the entire original boundary mark.
See Dehn derivation 016. -/
theorem exists_vertexLink_edge_in_subcomplex
    (A : SimplicialComplex ℝ E) (hAK : A ≤ K)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, s ⊆ t ∧ t.card = 3)
    {p : E} (hp : p ∈ A.vertices) :
    ∃ e ∈ (K.faceLink {p}).faces, e.card = 2 ∧ insert p e ∈ A.faces := by
  obtain ⟨t, ht, hpt, htc⟩ := hpure {p} hp
  have hpmem : p ∈ t := hpt (Finset.mem_singleton_self p)
  have hec : (t.erase p).card = 2 := by
    rw [Finset.card_erase_of_mem hpmem, htc]
  have hne : (t.erase p).Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨t.erase p, ⟨K.down_closed (hAK ht) (Finset.erase_subset _ _) hne,
    Finset.disjoint_singleton_left.mpr (Finset.notMem_erase _ _), ?_⟩, hec, ?_⟩
  · simpa only [Finset.singleton_union, Finset.insert_erase hpmem] using hAK ht
  · simpa only [Finset.insert_erase hpmem] using ht

end Geometry.SimplicialComplex
