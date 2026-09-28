import PoincareConjecture.Proofs.M76.Rigidity.OriginalIncidentEdgeLink

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in

theorem mem_boundary_vertex_base_endpoints_iff (p : (T.marked 2).vertices)
    (hpfront : (p : T.index → ℝ × V3) ∈ (T.marked 1).space)
    (x : T.index → ℝ × V3) :
    x ∈ (T.diskDualBase {(p : T.index → ℝ × V3)} ∩ (T.marked 1).space) ∩
        ((T.vertexBlock p).link p).space ↔
      ∃ s : Finset (T.index → ℝ × V3), s ∈ (T.marked 2).faces ∧
        s ∈ (T.marked 1).faces ∧ (p : T.index → ℝ × V3) ∈ s ∧
        s.card = 2 ∧ s.centroid ℝ id = x := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
  let : Fintype (T.marked 3).faces := (T.marked_finite 3).fintype
  let N := T.vertexBlock p
  let M := (T.marked 3).barycentricDualBlock {(p : T.index → ℝ × V3)}
  have hpB : {(p : T.index → ℝ × V3)} ∈ (T.marked 1).faces :=
    (SimplicialComplex.vertex_mem_subcomplex_space_iff (T.marked_le 1)
      (T.marked_le 2 p.property)).mp hpfront
  have hpQ : {(p : T.index → ℝ × V3)} ∈ (T.marked 3).faces :=
    (T.disk_face_mem_boundary_iff p.property).mp hpB
  have hM : T.diskDualBase {(p : T.index → ℝ × V3)} ∩ (T.marked 1).space = M.space := by
    change (T.dualRegion {(p : T.index → ℝ × V3)} ∩ (T.marked 2).space) ∩
      (T.marked 1).space = M.space
    rw [T.dualRegion_inter_disk, T.disk_dual_inter_boundary]
  have hstar : M.closedStar p = M := by
    simpa only [Finset.centroid_singleton, id_eq] using
      (T.marked 3).barycentricDualBlock_closedStar_faceCentroid hpQ
  have hlink : (M.link p).space = M.space ∩ (N.link p).space :=
    SimplicialComplex.link_space_eq_inter_of_closedStar_eq N M
      (T.ambient.barycentricDualBlock_mono_of_subcomplex
        (T.marked 3) (T.marked_le 3) {(p : T.index → ℝ × V3)}) p hstar
  rw [hM, ← hlink]
  constructor
  · intro hx
    obtain ⟨f, hf, hxf⟩ := SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨a, ha, hfaces, hchain, hfa⟩ :=
      ((T.marked 3).barycentricSubdivision_faces_of_face_chains f).mp hf.1.1
    have hdata (u : Finset (T.index → ℝ × V3)) (hu : u ∈ a) :
        (p : T.index → ℝ × V3) ∈ u ∧ u.card = 2 := by
      have hcu : u.centroid ℝ id ∈ f := by
        rw [hfa]
        exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
      obtain ⟨v, hv, hpv, hvu⟩ := hf.1.2 _ hcu
      have he : (⟨v, hv⟩ : (T.marked 3).faces) = ⟨u, hfaces u hu⟩ :=
        (T.marked 3).faceCentroid_injective hvu
      have hvu' : v = u := congrArg Subtype.val he
      have hpu : (p : T.index → ℝ × V3) ∈ u :=
        hvu' ▸ hpv (Finset.mem_singleton_self _)
      have hne : {(p : T.index → ℝ × V3)} ≠ u := by
        intro hueq
        apply hf.2.1
        simpa only [← hueq, Finset.centroid_singleton, id_eq] using hcu
      have hlt := Finset.card_lt_card
        ((Finset.singleton_subset_iff.mpr hpu).ssubset_of_ne hne)
      have hle := T.rim_face_card_le (hfaces u hu)
      rw [Finset.card_singleton] at hlt
      exact ⟨hpu, by omega⟩
    obtain ⟨s, hs⟩ := ha
    have hsame (u : Finset (T.index → ℝ × V3)) (hu : u ∈ a) : u = s := by
      rcases hchain u hu s hs with h | h
      · exact Finset.eq_of_subset_of_card_le h (by rw [(hdata u hu).2, (hdata s hs).2])
      · exact (Finset.eq_of_subset_of_card_le h
          (by rw [(hdata u hu).2, (hdata s hs).2])).symm
    have hsub : (f : Set (T.index → ℝ × V3)) ⊆ {s.centroid ℝ id} := by
      intro y hy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (hfa ▸ hy)
      exact congrArg (fun v : Finset (T.index → ℝ × V3) => v.centroid ℝ id) (hsame u hu)
    have hxs : x = s.centroid ℝ id := by
      simpa only [convexHull_singleton, mem_singleton_iff] using convexHull_mono hsub hxf
    exact ⟨s, T.rim_le_disk (hfaces s hs), T.rim_le_boundary (hfaces s hs),
      (hdata s hs).1, (hdata s hs).2, hxs.symm⟩
  · rintro ⟨s, hsD, hsB, hps, hcard, rfl⟩
    have hsQ := (T.disk_face_mem_boundary_iff hsD).mp hsB
    have hstrict : {(p : T.index → ℝ × V3)} ≠ s := by
      intro heq
      have hc := congrArg Finset.card heq
      simp only [Finset.card_singleton, hcard] at hc
      omega
    simpa only [Finset.centroid_singleton, id_eq] using
      (T.marked 3).cofaceCentroid_mem_dualBlock_link hpQ hsQ
        (Finset.singleton_subset_iff.mpr hps) hstrict

end PoincareConjecture.M76.OriginalProperDiskTriangulation
