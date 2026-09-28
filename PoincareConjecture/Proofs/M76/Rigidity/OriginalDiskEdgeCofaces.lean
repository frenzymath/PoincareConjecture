import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskParameter
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence
import PoincareConjecture.Proofs.M76.Mathlib.InteriorFacetLinks










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)




theorem exists_rim_edge_triangle_coface
    {s : Finset (T.index → ℝ × V3)} (hs : s ∈ (T.marked 2).faces)
    (hscard : s.card = 2) (hsQ : s ∈ (T.marked 3).faces) :
    ∃ t ∈ (T.marked 2).faces, s ⊆ t ∧ t.card = 3 ∧
      ∀ v ∈ (T.marked 2).faces, s ⊆ v → v.card = 3 → v = t := by
  classical
  let K := T.marked 2
  have hf : K.AffineOnFaces T.parameter :=
    fun t ht => T.parameter_affine t (T.marked_le 2 ht)
  obtain ⟨hi, himage⟩ := T.disk_parameter_image
  let L := hf.embeddedImage hi
  let q := s.image T.parameter
  have hLs : L.space = D := (hf.embeddedImage_space hi).trans himage
  have hq : q ∈ L.faces :=
    (hf.image_mem_embeddedImage_iff hi (K.subset_space hs)).mpr hs
  have hqc : q.card = Module.finrank ℝ V2 := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hscard] using
      (Finset.card_image_iff.mpr (hi.mono (K.subset_space hs)))
  have hqfront : convexHull ℝ (q : Set V2) ⊆ frontier L.space := by
    intro y hy
    have hyim : y ∈ T.parameter '' convexHull ℝ (s : Set (T.index → ℝ × V3)) := by
      rw [hf.image_convexHull hs]
      simpa only [q, Finset.coe_image] using hy
    obtain ⟨x, hx, rfl⟩ := hyim
    rw [hLs, frontier_closedBall']
    exact (T.rim_parameter_image).2.subset
      (mem_image_of_mem T.parameter ((T.marked 3).convexHull_subset_space hsQ hx))
  obtain ⟨t, ht, hst, htc⟩ := T.exists_disk_triangle_coface hs
  refine ⟨t, ht, hst, htc, ?_⟩
  intro v hv hsv hvc
  by_contra hvne
  have htL : t.image T.parameter ∈ L.faces :=
    (hf.image_mem_embeddedImage_iff hi (K.subset_space ht)).mpr ht
  have hvL : v.image T.parameter ∈ L.faces :=
    (hf.image_mem_embeddedImage_iff hi (K.subset_space hv)).mpr hv
  have htcL : (t.image T.parameter).card = Module.finrank ℝ V2 + 1 := by
    simpa [htc] using Finset.card_image_iff.mpr (hi.mono (K.subset_space ht))
  have hvcL : (v.image T.parameter).card = Module.finrank ℝ V2 + 1 := by
    simpa [hvc] using Finset.card_image_iff.mpr (hi.mono (K.subset_space hv))
  have hneL : t.image T.parameter ≠ v.image T.parameter := by
    intro he
    have him : T.parameter '' (t : Set (T.index → ℝ × V3)) =
        T.parameter '' (v : Set (T.index → ℝ × V3)) := by
      simpa only [Finset.coe_image] using
        congrArg (fun a : Finset V2 => (a : Set V2)) he
    have htv : t = v := Finset.coe_injective
      ((hi.image_eq_image_iff (K.subset_space ht) (K.subset_space hv)).mp him)
    exact hvne htv.symm
  obtain ⟨y, hy⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ (q : Set V2))
    (Finset.coe_nonempty.mpr (L.nonempty_of_mem_faces hq)).convexHull
  have hyint := L.mem_interior_space_of_paired_facet hqc htL hvL htcL hvcL
    (Finset.image_subset_image hst) (Finset.image_subset_image hsv) hneL hy
  exact (hqfront (intrinsicInterior_subset hy)).2 hyint





theorem exists_interior_edge_triangle_cofaces
    {s : Finset (T.index → ℝ × V3)} (hs : s ∈ (T.marked 2).faces)
    (hscard : s.card = 2) (hsQ : s ∉ (T.marked 3).faces) :
    ∃ t ∈ (T.marked 2).faces, ∃ v ∈ (T.marked 2).faces,
      s ⊆ t ∧ s ⊆ v ∧ t.card = 3 ∧ v.card = 3 ∧ t ≠ v ∧
      ∀ u ∈ (T.marked 2).faces, s ⊆ u → u.card = 3 → u = t ∨ u = v := by
  classical
  let K := T.marked 2
  have hf : K.AffineOnFaces T.parameter :=
    fun t ht => T.parameter_affine t (T.marked_le 2 ht)
  obtain ⟨hi, himage⟩ := T.disk_parameter_image
  let L := hf.embeddedImage hi
  have hL : L.faces.Finite := hf.embeddedImage_finite hi (T.marked_finite 2)
  have hLs : L.space = D := (hf.embeddedImage_space hi).trans himage
  have hsL : s.image T.parameter ∈ L.faces :=
    (hf.image_mem_embeddedImage_iff hi (K.subset_space hs)).mpr hs
  have hscL : (s.image T.parameter).card = Module.finrank ℝ V2 := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hscard] using
      (Finset.card_image_iff.mpr (hi.mono (K.subset_space hs)))
  obtain ⟨p, hps, hpQ⟩ := SimplicialComplex.exists_vertex_off_full_subcomplex
    (T.marked_le 3) (T.marked_full 3) (T.marked_le 2 hs) hsQ
  have hpK : p ∈ K.space := K.subset_space hs hps
  have hpD : T.parameter p ∈ D := himage.subset (mem_image_of_mem T.parameter hpK)
  have hpint : T.parameter p ∈ interior D := by
    apply (mem_interior_iff_notMem_frontier hpD).mpr
    rw [frontier_closedBall']
    exact fun h => hpQ ((T.parameter_mem_rim_iff hpK).mp h)
  have hcount := L.faceLink_ncard_eq_two_of_hull_meets_interior hL hsL hscL
    ⟨T.parameter p, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩),
      hLs.symm ▸ hpint⟩
  rw [hf.ncard_embeddedImage_faceLink hi hs, K.ncard_faceLink_vertices_eq_cofaces,
    hscard] at hcount
  obtain ⟨t, v, htv, heq⟩ := ncard_eq_two.mp hcount
  have ht : t ∈ {u : Finset (T.index → ℝ × V3) |
      u ∈ K.faces ∧ u.card = 3 ∧ s ⊆ u} := heq.symm.subset (Or.inl rfl)
  have hv : v ∈ {u : Finset (T.index → ℝ × V3) |
      u ∈ K.faces ∧ u.card = 3 ∧ s ⊆ u} := heq.symm.subset (Or.inr rfl)
  exact ⟨t, ht.1, v, hv.1, ht.2.2, hv.2.2, ht.2.1, hv.2.1, htv,
    fun u hu hsu huc => heq.subset ⟨hu, huc, hsu⟩⟩

end PoincareConjecture.M76.OriginalProperDiskTriangulation
