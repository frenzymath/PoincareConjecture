import PoincareConjecture.Proofs.M76.Mathlib.PolygonTriangulationData
import PoincareConjecture.Proofs.M76.Mathlib.PolygonTriangleRegion









set_option autoImplicit false

open Set Geometry

namespace Polygon



theorem exists_triangle_triangulation (P : Polygon (ℝ × ℝ) 3)
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    ∃ K : SimplicialComplex ℝ (ℝ × ℝ), P.IsTriangulation K := by
  classical
  let V := Finset.univ.image P
  have hV : (V : Set (ℝ × ℝ)) = range P := by simp [V]
  have hind : AffineIndependent ℝ ((↑) : V → ℝ × ℝ) := by
    change AffineIndependent ℝ ((↑) : ↥(V : Set (ℝ × ℝ)) → ℝ × ℝ)
    rw [hV]
    exact (P.affineIndependent_triangle hP hinj).range
  have hgen : ∀ s ∈ ({V} : Set (Finset (ℝ × ℝ))),
      AffineIndependent ℝ ((↑) : s → ℝ × ℝ) := by
    rintro s rfl
    exact hind
  have hinter : ∀ s ∈ ({V} : Set (Finset (ℝ × ℝ))), ∀ t ∈ ({V} : Set (Finset (ℝ × ℝ))),
      convexHull ℝ (s : Set (ℝ × ℝ)) ∩ convexHull ℝ (t : Set (ℝ × ℝ)) ⊆
        convexHull ℝ ((s : Set (ℝ × ℝ)) ∩ t) := by
    rintro s rfl t rfl
    simp
  let K := SimplicialComplex.ofGenerators {V} hgen hinter
  have hfaces (s) : s ∈ K.faces ↔ s.Nonempty ∧ s ⊆ V := by
    simp [K, SimplicialComplex.mem_ofGenerators_faces]
  have hcard : V.card = 3 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  refine ⟨K, ?_⟩
  constructor
  · exact SimplicialComplex.finite_ofGenerators_faces (finite_singleton V) hgen hinter
  · rw [SimplicialComplex.space_ofGenerators]
    simp only [biUnion_singleton]
    rw [hV, P.closure_inside_triangle hP hinj]
  · intro x hx
    have hxV : x ∈ V := (hfaces {x}).mp hx |>.2 (Finset.mem_singleton_self x)
    exact hV ▸ hxV
  · intro i
    apply (hfaces _).mpr
    constructor
    · simp [edgeVertices]
    · simp [edgeVertices, V, Finset.insert_subset_iff, Finset.singleton_subset_iff]
  · intro s hs
    refine ⟨V, (hfaces V).mpr ⟨?_, Finset.Subset.refl V⟩, (hfaces s).mp hs |>.2, hcard⟩
    exact Finset.card_pos.mp (by omega)

end Polygon
