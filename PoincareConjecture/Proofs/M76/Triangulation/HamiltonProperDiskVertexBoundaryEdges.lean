import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexBase










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "Cube" => closedBall (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : Cube ≃ₜ D}

omit [FiniteDimensional ℝ E] in



theorem HamiltonProperDiskTriangulation.edge_dual_subset_vertex_link
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices)
    {s : Finset E} (hs : s ∈ T.disk.faces) (hcard : s.card = 2) (hps : (p : E) ∈ s) :
    let : Fintype T.ambient.faces := T.finite.fintype
    (T.ambient.barycentricDualBlock s).space ⊆ ((T.vertexBlock p).link p).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let N := T.vertexBlock p
  have hpK : {(p : E)} ∈ T.ambient.faces := T.ambient.down_closed (T.disk_le hs)
    (Finset.singleton_subset_iff.mpr hps) (Finset.singleton_nonempty _)
  have hstar : N.closedStar p = N := (T.vertexBlock_centered_chart p).2.2.1
  change (T.ambient.barycentricDualBlock s).space ⊆ (N.link p).space
  intro x hx
  obtain ⟨f, hf, hxf⟩ := SimplicialComplex.mem_space_iff.mp hx
  have hfN : f ∈ N.faces := T.ambient.barycentricDualBlock_antitone
    (Finset.singleton_subset_iff.mpr hps) hf
  have hpnot : (p : E) ∉ f := by
    intro hpf
    obtain ⟨u, hu, hsu, hup⟩ := hf.2 p hpf
    have he : (⟨u, hu⟩ : T.ambient.faces) = ⟨{(p : E)}, hpK⟩ :=
      T.ambient.faceCentroid_injective (by
        simpa only [Finset.centroid_singleton, id_eq] using hup)
    have huone : u = {(p : E)} := congrArg Subtype.val he
    have hle := Finset.card_le_card hsu
    rw [huone, Finset.card_singleton, hcard] at hle
    omega
  have hfst : f ∈ (N.closedStar p).faces := hstar.symm ▸ hfN
  exact (N.link p).convexHull_subset_space ⟨hfN, hpnot, hfst.2⟩ hxf




theorem HamiltonProperDiskTriangulation.mem_boundary_vertex_base_endpoints_iff
    (T : HamiltonProperDiskTriangulation R D b)
    (hproper : ∀ x : Cube, (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1)
    (p : T.disk.vertices) (x : E) :
    x ∈ (T.diskVertexBlock p ∩ frontier R) ∩ ((T.vertexBlock p).link p).space ↔
      ∃ s : Finset E, s ∈ T.disk.faces ∧ s ∈ T.boundary.faces ∧
        (p : E) ∈ s ∧ s.card = 2 ∧ s.centroid ℝ id = x := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype T.disk.faces := (T.finite.subset T.disk_le).fintype
  let : Fintype T.boundary.faces := (T.finite.subset T.boundary_le).fintype
  let K := T.ambient.barycentricSubdivision
  let N := T.vertexBlock p
  let B := T.disk.barycentricDualBlock {(p : E)}
  let M := T.boundary.barycentricSubdivision
  have hBK : B ≤ K := (T.disk.barycentricDualBlock_le {(p : E)}).trans
    (T.disk.barycentricSubdivision_mono T.disk_le)
  have hLK : N.link p ≤ K := (show N.link p ≤ N from fun _ hs => hs.1).trans
    (T.ambient.barycentricDualBlock_le {(p : E)})
  have hMK : M ≤ K := T.boundary.barycentricSubdivision_mono T.boundary_le
  constructor
  · intro hx
    have hxB : x ∈ B.space := hx.1.1
    obtain ⟨f, hfB, hfL, hxf⟩ := K.exists_common_face_of_mem_subcomplexes
      B (N.link p) hBK hLK ⟨hxB, hx.2⟩
    have hxM : x ∈ M.space :=
      T.boundary.barycentricSubdivision_isSubdivision.space_eq.symm.subset
        (T.boundary_space.symm.subset hx.1.2)
    obtain ⟨t, htM, hxt⟩ := SimplicialComplex.mem_space_iff.mp hxM
    let g := f ∩ t
    have hxg : x ∈ convexHull ℝ (g : Set E) := by
      simpa only [g, Finset.coe_inter] using
        K.inter_subset_convexHull (hBK hfB) (hMK htM) ⟨hxf, hxt⟩
    have hgne : g.Nonempty := convexHull_nonempty_iff.mp ⟨x, hxg⟩
    have hgB : g ∈ B.faces := B.down_closed hfB Finset.inter_subset_left hgne
    have hgL : g ∈ (N.link p).faces :=
      (N.link p).down_closed hfL Finset.inter_subset_left hgne
    have hgM : g ∈ M.faces := M.down_closed htM Finset.inter_subset_right hgne
    obtain ⟨a, ha, hfaces, hchain, hga⟩ :=
      (T.ambient.barycentricSubdivision_faces_of_face_chains g).mp (hBK hgB)
    have hdata (u : Finset E) (hu : u ∈ a) :
        u ∈ T.disk.faces ∧ u ∈ T.boundary.faces ∧ (p : E) ∈ u ∧ u.card = 2 := by
      have hcu : u.centroid ℝ id ∈ g := by
        rw [hga]
        exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
      obtain ⟨v, hv, hpv, hvu⟩ := hgB.2 _ hcu
      have he : (⟨v, T.disk_le hv⟩ : T.ambient.faces) = ⟨u, hfaces u hu⟩ :=
        T.ambient.faceCentroid_injective hvu
      have hvu' : v = u := congrArg Subtype.val he
      have huD : u ∈ T.disk.faces := hvu' ▸ hv
      have hpu : (p : E) ∈ u := hvu' ▸ hpv (Finset.mem_singleton_self _)
      have huF : u ∈ T.boundary.faces :=
        (T.ambient.faceCentroid_mem_barycentricSubdivision_iff T.boundary_le
          ⟨u, hfaces u hu⟩).mp (M.face_subset_vertices hgM hcu)
      have hne : u ≠ {(p : E)} := by
        intro hueq
        apply hgL.2.1
        simpa only [hueq, Finset.centroid_singleton, id_eq] using hcu
      have hcardpos : 0 < u.card := Finset.card_pos.mpr (T.disk.nonempty_of_mem_faces huD)
      have hcardone : u.card ≠ 1 := by
        intro hc
        apply hne
        exact (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hpu)
          (by simpa only [Finset.card_singleton] using hc.le)).symm
      have hcardthree : u.card ≠ 3 :=
        fun hc => T.disk_triangle_not_boundary hproper huD hc huF
      have hle := T.disk_face_card_le huD
      exact ⟨huD, huF, hpu, by omega⟩
    obtain ⟨s, hs⟩ := ha
    have hsdata := hdata s hs
    have hverts : (g : Set E) ⊆ {s.centroid ℝ id} := by
      intro y hy
      obtain ⟨u, hu, huy⟩ := Finset.mem_image.mp (hga ▸ hy)
      have hudata := hdata u hu
      have hus : u = s := by
        rcases hchain u hu s hs with h | h
        · exact Finset.eq_of_subset_of_card_le h (by rw [hudata.2.2.2, hsdata.2.2.2])
        · exact (Finset.eq_of_subset_of_card_le h
            (by rw [hudata.2.2.2, hsdata.2.2.2])).symm
      change y = s.centroid ℝ id
      exact huy.symm.trans (congrArg (fun z : Finset E => z.centroid ℝ id) hus)
    have hxs : x = s.centroid ℝ id := by
      simpa only [convexHull_singleton, mem_singleton_iff] using convexHull_mono hverts hxg
    exact ⟨s, hsdata.1, hsdata.2.1, hsdata.2.2.1, hsdata.2.2.2, hxs.symm⟩
  · rintro ⟨s, hsD, hsF, hps, hcard, rfl⟩
    have hstrict : {(p : E)} ≠ s := by
      intro heq
      have hc := congrArg Finset.card heq
      simp only [Finset.card_singleton, hcard] at hc
      omega
    have hcsB : s.centroid ℝ id ∈ B.space := by
      have h := T.disk.cofaceCentroid_mem_dualBlock_link p.property hsD
        (Finset.singleton_subset_iff.mpr hps) hstrict
      have hle : (B.link (({(p : E)} : Finset E).centroid ℝ id)).space ⊆ B.space :=
        SimplicialComplex.space_subset_of_le
          (show B.link (({(p : E)} : Finset E).centroid ℝ id) ≤ B from fun _ hf => hf.1)
      exact hle h
    have hcsF : s.centroid ℝ id ∈ frontier R := T.boundary_space.subset
      (T.boundary.convexHull_subset_space hsF
        (s.centroid_mem_convexHull (T.boundary.nonempty_of_mem_faces hsF)))
    have hcsN : s.centroid ℝ id ∈ (T.ambient.barycentricDualBlock s).space :=
      (T.ambient.barycentricDualBlock s).vertices_subset_space
        (T.ambient.faceCentroid_mem_barycentricDualBlock_vertices (T.disk_le hsD))
    exact ⟨⟨hcsB, hcsF⟩, T.edge_dual_subset_vertex_link p hsD hcard hps hcsN⟩

end PoincareConjecture.M76.HamiltonIndexOne
