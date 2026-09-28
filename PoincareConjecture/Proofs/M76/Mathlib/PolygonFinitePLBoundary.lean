import PoincareConjecture.Proofs.M76.Mathlib.PolygonBoundaryHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph

set_option autoImplicit false

open Set

namespace Polygon

theorem exists_finitePL_boundary_edge_coordinates {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {n : ℕ}
    (P : Polygon E (n + 3)) (Q : Polygon F (n + 3))
    (hP : P.HasSimplicialEdges) (hQ : Q.HasSimplicialEdges)
    (hinjP : Function.Injective P) (hinjQ : Function.Injective Q) :
    ∃ e : P.boundary ℝ ≃ₜ Q.boundary ℝ, e.IsFinitePL ∧
      ∀ (i : Fin (n + 3)) (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1)
        (hx : AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) t ∈ P.boundary ℝ),
        (e ⟨AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) t, hx⟩ : F) =
          AffineMap.lineMap (Q i) (Q (finRotate (n + 3) i)) t := by
  obtain ⟨f, _, H, hf, _, hfv, _, hH, _⟩ :=
    P.exists_simplicial_homeomorph Q hP hQ hinjP hinjQ
  let e := ((Homeomorph.setCongr (P.simplicialComplex_space hP).symm).trans H).trans
    (Homeomorph.setCongr (Q.simplicialComplex_space hQ))
  have he (x : P.boundary ℝ) : (e x : F) = f x := hH _
  refine ⟨e, ⟨f, ⟨P.simplicialComplex hP, P.finite_simplicialComplex_faces hP,
    P.simplicialComplex_space hP, hf⟩, he⟩, ?_⟩
  intro i t ht hx
  obtain ⟨a, ha⟩ := hf _ (P.edgeVertices_mem_faces hP i)
  have hp : a (P i) = Q i :=
    (ha (subset_convexHull ℝ _ (by simp [edgeVertices]))).symm.trans (hfv i)
  have hq : a (P (finRotate (n + 3) i)) = Q (finRotate (n + 3) i) :=
    (ha (subset_convexHull ℝ _ (by simp [edgeVertices]))).symm.trans (hfv _)
  rw [he, ha, a.apply_lineMap, hp, hq]
  rw [← P.edgeSet_eq_convexHull]
  exact ⟨t, ht, rfl⟩

end Polygon
