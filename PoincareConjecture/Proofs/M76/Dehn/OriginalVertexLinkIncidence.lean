import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VertexLinkTriangleIncidence
import PoincareConjecture.Proofs.M76.Dehn.OriginalChartConnectedLinks
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalBoundaryLinks
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalChartStarPurity

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]

open Classical in

theorem original_chart_stars_vertex_link_incidence
    (K A : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hAK : A ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ p ∈ s, p ∈ A.vertices) → s ∈ A.faces)
    {R : Set X} (hFR : frontier R ⊆ R) (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hboundary : ∀ z ∈ K.space, (g z : X) ∈ frontier R ↔ z ∈ A.space)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)))
    {p : E} (hp : p ∈ K.vertices) :
    let Q := K.faceLink {p}
    (∀ s ∈ Q.faces, ∃ t ∈ Q.faces, s ⊆ t ∧ t.card = 3) ∧
      IsConnected Q.space ∧
      (∀ q ∈ Q.vertices, IsConnected (Q.faceLink {q}).space) ∧
      (∀ e ∈ Q.faces, e.card = 2 →
        {t : Finset E | t ∈ Q.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard =
          if insert p e ∈ A.faces then 1 else 2) ∧
      (p ∈ A.vertices → ∃ e ∈ Q.faces, e.card = 2 ∧
        {t : Finset E | t ∈ Q.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 1) ∧
      (p ∉ A.vertices → ∀ e ∈ Q.faces, e.card = 2 →
        {t : Finset E | t ∈ Q.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) := by
  classical
  let Q := K.faceLink {p}
  have hpure := exists_tetrahedral_coface_of_original_chart_stars K hK H g hg hstars
  have hfac := original_chart_stars_facet_incidence
    K hK A hAK hfull H g hg hboundary hpure hstars
  have hlinks := original_chart_stars_connected_links
    K hK A hAK hfull H g hg hboundary hstars
  have hcount (e : Finset E) (he : e ∈ Q.faces) (hec : e.card = 2) :
      {t : Finset E | t ∈ Q.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard =
        if insert p e ∈ A.faces then 1 else 2 := by
    rw [K.vertexLink_triangle_cofaces_ncard he hec]
    have hjoin : insert p e ∈ K.faces := by
      simpa only [Finset.singleton_union] using he.2.2
    have hcard : (insert p e).card = 3 := by
      rw [Finset.card_insert_of_notMem (Finset.disjoint_singleton_left.mp he.2.1), hec]
    by_cases hb : insert p e ∈ A.faces
    · rw [if_pos hb]
      exact (hfac _ hjoin hcard).1 hb
    · rw [if_neg hb]
      exact (hfac _ hjoin hcard).2 hb
  refine ⟨K.faceLink_singleton_triangular_pure hpure p,
    hlinks {p} hp (by simp), ?_, hcount, ?_, ?_⟩
  · intro q hq
    rw [K.faceLink_faceLink _ _ hq.2.1]
    apply hlinks _ hq.2.2
    have hpq : p ≠ q := by
      simpa only [Finset.disjoint_singleton_left, Finset.mem_singleton] using hq.2.1
    rw [Finset.singleton_union, Finset.card_pair hpq]
    omega
  · intro hpA
    have hsurface := original_boundary_surface_incidence
      K A hK hAK hFR H g hg hboundary hstars
    obtain ⟨e, he, hec, heA⟩ := K.exists_vertexLink_edge_in_subcomplex A hAK hsurface.1 hpA
    refine ⟨e, he, hec, ?_⟩
    rw [hcount e he hec, if_pos heA]
  · intro hpA e he hec
    rw [hcount e he hec, if_neg
      (SimplicialComplex.insert_notMem_faces_of_vertex_off_subcomplex A hpA e)]

end PoincareConjecture.M76
