import PoincareConjecture.Proofs.M76.Mathlib.RegularSlicePolygons
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCircle











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

omit [FiniteDimensional ℝ E] in


theorem finite_regularSliceGraph_components (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) (hK : K.faces.Finite) :
    Finite (K.regularSliceGraph A).ConnectedComponent := by
  let : Finite (K.regularCrossingEdges A) := (K.finite_regularCrossingEdges A hK).to_subtype
  infer_instance





theorem exists_regularSlice_polygonal_circles (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) (hK : K.faces.Finite) (hreg : ∀ v ∈ K.vertices, A v ≠ 0)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    ∃ (n : (K.regularSliceGraph A).ConnectedComponent → ℕ)
      (P : ∀ C, Polygon E (n C + 3)),
      (∀ C, Function.Injective (P C) ∧ (P C).HasSimplicialEdges ∧
        Nonempty ((P C).boundary ℝ ≃ₜ Circle)) ∧
      K.space ∩ {x | A x = 0} = ⋃ C, (P C).boundary ℝ ∧
      Pairwise (fun C D => Disjoint ((P C).boundary ℝ) ((P D).boundary ℝ)) := by
  obtain ⟨n, P, hP, hcover, hdisj⟩ := K.exists_regularSlice_polygons A hK hreg hpure hcofaces
  exact ⟨n, P, fun C => ⟨(hP C).1, (hP C).2,
    (P C).nonempty_boundary_homeomorph_circle (hP C).2 (hP C).1⟩, hcover, hdisj⟩

end Geometry.SimplicialComplex
