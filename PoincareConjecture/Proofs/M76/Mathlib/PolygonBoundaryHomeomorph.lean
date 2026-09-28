import PoincareConjecture.Proofs.M76.Mathlib.SimplicialPolygon
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialHomeomorph









set_option autoImplicit false

open Set Geometry

namespace Polygon

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

private theorem vertex_assignment_preserves_faces (P : Polygon E n) (Q : Polygon F n)
    (hP : P.HasSimplicialEdges) (hQ : Q.HasSimplicialEdges)
    (v : E → F) (hv : ∀ i, v (P i) = Q i) :
    ∀ s ∈ (P.simplicialComplex hP).faces,
      ∃ t ∈ (Q.simplicialComplex hQ).faces, v '' (s : Set E) ⊆ (t : Set F) := by
  classical
  intro s hs
  obtain ⟨_, i, hsi⟩ := (P.mem_simplicialComplex_faces hP s).mp hs
  refine ⟨Q.edgeVertices i, Q.edgeVertices_mem_faces hQ i, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hchoice : x = P i ∨ x = P (finRotate n i) := by
    simpa only [edgeVertices, Finset.mem_insert, Finset.mem_singleton] using hsi hx
  rcases hchoice with rfl | rfl
  · rw [hv]
    exact Finset.mem_insert_self _ _
  · rw [hv]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]




theorem exists_simplicial_homeomorph (P : Polygon E (n + 3)) (Q : Polygon F (n + 3))
    (hP : P.HasSimplicialEdges) (hQ : Q.HasSimplicialEdges)
    (hinjP : Function.Injective P) (hinjQ : Function.Injective Q) :
    ∃ (f : E → F) (g : F → E)
      (e : (P.simplicialComplex hP).space ≃ₜ (Q.simplicialComplex hQ).space),
      (P.simplicialComplex hP).AffineOnFaces f ∧
      (Q.simplicialComplex hQ).AffineOnFaces g ∧
      (∀ i, f (P i) = Q i) ∧ (∀ i, g (Q i) = P i) ∧
      (∀ x, (e x : F) = f x) ∧ (∀ y, (e.symm y : E) = g y) := by
  classical
  let v : E → F := fun x => Q (Function.invFun P x)
  let w : F → E := fun y => P (Function.invFun Q y)
  have hv (i) : v (P i) = Q i := congrArg Q (Function.leftInverse_invFun hinjP i)
  have hw (i) : w (Q i) = P i := congrArg P (Function.leftInverse_invFun hinjQ i)
  obtain ⟨f, g, e, hf, hg, hfv, hgw, hef, heg⟩ :=
    (P.simplicialComplex hP).exists_homeomorph_of_vertex_maps (Q.simplicialComplex hQ)
      (P.finite_simplicialComplex_faces hP) v w
      (vertex_assignment_preserves_faces P Q hP hQ v hv)
      (vertex_assignment_preserves_faces Q P hQ hP w hw)
      (by
        intro x hx
        rw [P.simplicialComplex_vertices hP] at hx
        obtain ⟨i, rfl⟩ := hx
        rw [hv, hw])
      (by
        intro y hy
        rw [Q.simplicialComplex_vertices hQ] at hy
        obtain ⟨i, rfl⟩ := hy
        rw [hw, hv])
  refine ⟨f, g, e, hf, hg, ?_, ?_, hef, heg⟩
  · intro i
    exact (hfv (by rw [P.simplicialComplex_vertices]; exact mem_range_self i)).trans (hv i)
  · intro i
    exact (hgw (by rw [Q.simplicialComplex_vertices]; exact mem_range_self i)).trans (hw i)




theorem nonempty_boundary_homeomorph (P : Polygon E (n + 3)) (Q : Polygon F (n + 3))
    (hP : P.HasSimplicialEdges) (hQ : Q.HasSimplicialEdges)
    (hinjP : Function.Injective P) (hinjQ : Function.Injective Q) :
    Nonempty (P.boundary ℝ ≃ₜ Q.boundary ℝ) := by
  obtain ⟨_, _, e, _⟩ := P.exists_simplicial_homeomorph Q hP hQ hinjP hinjQ
  exact ⟨((Homeomorph.setCongr (P.simplicialComplex_space hP).symm).trans e).trans
    (Homeomorph.setCongr (Q.simplicialComplex_space hQ))⟩

end Polygon
