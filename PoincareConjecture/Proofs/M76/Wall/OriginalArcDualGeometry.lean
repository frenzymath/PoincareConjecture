import PoincareConjecture.Proofs.M76.Wall.OriginalInteriorVertexDual
import PoincareConjecture.Proofs.M76.Wall.OriginalExteriorVertexHalfBall
import PoincareConjecture.Proofs.M76.Wall.OriginalInteriorEdgeDual
import PoincareConjecture.Proofs.M76.Wall.OriginalArcInteriorEndpoint
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ArcDualBoundaryAvoidance

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem original_arc_dual_geometry
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {C L : Set X} (hL : IsClosed L) (hLC : L ⊆ interior C)
    (K A D : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype D.faces]
    (hAK : A ≤ K) (hDK : D ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ p ∈ s, p ∈ D.vertices) → s ∈ D.faces)
    (hfinite : (A.space ∩ D.space).Finite)
    (F : X → E) (H : (C \ interior L : Set X) ≃ₜ K.space)
    (g : E → (C \ interior L : Set X))
    (hHF : ∀ x : (C \ interior L : Set X), (H x : E) = F x)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hD : D.space = F '' frontier L)
    {q : ℝ → X} (hzero : q 0 ∈ frontier L) (hone : q 1 ∈ frontier L)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, q t ∉ L)
    (hqC : MapsTo q (Icc (0 : ℝ) 1) (interior C))
    (hgarc : MapsTo (fun z => (g z : X)) A.space (q '' Icc (0 : ℝ) 1))
    (hstars : ∀ p ∈ A.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      B.source ⊆ interior C ∧
      (B.source ⊆ Lᶜ ∨ ∃ (ell : V3 →L[ℝ] ℝ) (v : V3),
        ell v = 1 ∧ ∀ y ∈ B.source, y ∈ L ↔ 0 ≤ ell (B y))) :
    (∀ p ∈ A.vertices,
      IsFinitePLBallPair V3 (K.barycentricDualBlock {p}).space
        (((K.barycentricDualBlock {p}).link p).space ∪
          (D.barycentricDualBlock {p}).space) ∧
      (p ∈ D.vertices →
        IsFinitePLBallPair (ℝ × ℝ) ((K.barycentricDualBlock {p}).link p).space
          (((K.barycentricDualBlock {p}).link p).space ∩
            (D.barycentricDualBlock {p}).space) ∧
        IsFinitePLBallPair (ℝ × ℝ) (D.barycentricDualBlock {p}).space
          (((K.barycentricDualBlock {p}).link p).space ∩
            (D.barycentricDualBlock {p}).space))) ∧
    ∀ s ∈ A.faces, s.card = 2 →
      IsFinitePLBallPair (ℝ × ℝ) (K.barycentricDualBlock s).space
        ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space ∧
      Disjoint (K.barycentricDualBlock s).space D.space := by
  have hfrontR : frontier L ⊆ C \ interior L :=
    fun _ hx => ⟨interior_subset (hLC (hL.frontier_subset hx)), hx.2⟩
  have hgF (x : X) (hx : x ∈ C \ interior L) : (g (F x) : X) = x := by
    have h := hg (H ⟨x, hx⟩)
    rw [H.symm_apply_apply] at h
    simpa only [hHF] using h
  have hFg (z : E) (hz : z ∈ K.space) : F (g z) = z := by
    rw [hg ⟨z, hz⟩]
    exact (hHF (H.symm ⟨z, hz⟩)).symm.trans
      (congrArg Subtype.val (H.apply_symm_apply ⟨z, hz⟩))
  have hmark (z : E) (hz : z ∈ K.space) :
      (g z : X) ∈ frontier L ↔ z ∈ D.space := by
    rw [hD]
    constructor
    · intro hzb
      exact ⟨g z, hzb, hFg z hz⟩
    · rintro ⟨x, hxb, hxz⟩
      rw [← hxz, hgF x (hfrontR hxb)]
      exact hxb
  have hinterior (p : E) (hpA : p ∈ A.vertices) (hpD : p ∉ D.vertices) :
      (g p : X) ∈ interior (C \ interior L) := by
    have hpAs : p ∈ A.space := A.vertices_subset_space hpA
    have hnot : (g p : X) ∉ frontier L := by
      intro h
      exact hpD (mem_vertices_of_finite_subcomplex_intersection hAK hDK hfinite
        hpAs ((hmark p (space_subset_of_le hAK hpAs)).mp h)).2
    obtain ⟨t, ht, hgt⟩ := hgarc hpAs
    change q t = (g p : X) at hgt
    have ht0 : t ≠ 0 := by
      intro he
      apply hnot
      rw [← hgt, he]
      exact hzero
    have ht1 : t ≠ 1 := by
      intro he
      apply hnot
      rw [← hgt, he]
      exact hone
    have houtside : (g p : X) ∉ L := by
      rw [← hgt]
      exact hproper t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    have hopen : IsOpen (interior C \ L) := isOpen_interior.sdiff hL
    have hsub : interior C \ L ⊆ C \ interior L :=
      fun _ hx => ⟨interior_subset hx.1, fun hy => hx.2 (interior_subset hy)⟩
    exact interior_maximal hsub hopen ⟨hgt ▸ hqC ht, houtside⟩
  constructor
  · intro p hpA
    obtain ⟨B, hsource, hface, hinside, hregion⟩ := hstars p hpA
    by_cases hpD : p ∈ D.vertices
    · have hpK : p ∈ K.vertices := hDK hpD
      have hpstar : p ∈ (K.closedStar p).space := by
        apply (K.closedStar p).vertices_subset_space
        change {p} ∈ K.faces ∧ insert p {p} ∈ K.faces
        have hins : insert p ({p} : Finset E) = {p} :=
          Finset.insert_eq_of_mem (Finset.mem_singleton_self p)
        refine ⟨hpK, ?_⟩
        rw [hins]
        exact hpK
      have hgpL : (g p : X) ∈ L := hL.frontier_subset
        ((hmark p (K.vertices_subset_space hpK)).mpr (D.vertices_subset_space hpD))
      obtain ⟨ell, v, hv, hhalf⟩ : ∃ (ell : V3 →L[ℝ] ℝ) (v : V3),
          ell v = 1 ∧ ∀ y ∈ B.source, y ∈ L ↔ 0 ≤ ell (B y) := by
        rcases hregion with hout | hhalf
        · exact False.elim (hout (hsource hpstar) hgpL)
        · exact hhalf
      obtain ⟨G, hlink, hfoot⟩ := exists_original_exterior_vertex_half_ball
        hL hLC K D hDK F H g hHF hg hD hpD B hinside hsource hface ell v hv hhalf
      exact ⟨G.ball, fun _ => ⟨hlink, hfoot⟩⟩
    · have hball := isFinitePLBallPair_original_interior_vertex_dual K H g hg
        (hAK hpA) (hinterior p hpA hpD) B hsource hface
      have hempty := D.barycentricDualBlock_space_eq_empty_of_not_face
        (Finset.singleton_nonempty p) hpD
      refine ⟨?_, fun h => (hpD h).elim⟩
      simpa only [hempty, union_empty] using hball
  · intro s hs hcard
    obtain ⟨p, hps, hpR⟩ := exists_original_arc_edge_interior_endpoint hL
      hzero hone hproper hqC K A D hAK hDK hfull hfinite (fun z => (g z : X))
      hgarc (fun z hz => (hmark z (space_subset_of_le hAK hz)).mp) hs hcard
    obtain ⟨B, hsource, hface, _⟩ := hstars p (A.face_subset_vertices hs hps)
    exact ⟨isFinitePLBallPair_original_interior_edge_dual K H g hg
      (hAK hs) hcard hps hpR B hsource hface,
      (K.arc_edge_dual_disjoint_boundary A D hAK hDK hfull hfinite hs hcard).1⟩

end PoincareConjecture.M76
