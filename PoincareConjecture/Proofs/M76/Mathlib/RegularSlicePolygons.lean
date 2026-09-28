import PoincareConjecture.Proofs.M76.Mathlib.RegularSliceSegments
import PoincareConjecture.Proofs.M76.Mathlib.GeometricCyclePolygons










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]




theorem exists_regularSlice_polygons (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    (hK : K.faces.Finite) (hreg : ∀ v ∈ K.vertices, A v ≠ 0)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    ∃ (n : (K.regularSliceGraph A).ConnectedComponent → ℕ)
      (P : ∀ C, Polygon E (n C + 3)),
      (∀ C, Function.Injective (P C) ∧ (P C).HasSimplicialEdges) ∧
      K.space ∩ {x | A x = 0} = ⋃ C, (P C).boundary ℝ ∧
      Pairwise (fun C D => Disjoint ((P C).boundary ℝ) ((P D).boundary ℝ)) := by
  let : Finite (K.regularCrossingEdges A) := (K.finite_regularCrossingEdges A hK).to_subtype
  obtain ⟨n, P, hP, hcover, hdisj⟩ :=
    (K.regularSliceGraph A).exists_component_polygons_of_two_neighbors
      (K.regularCrossingPoint A hreg) (K.regularSliceGraph_two_neighbors A hcofaces)
      (K.regularCrossingPoint_injective A hreg)
      (fun {_ _ _ _} hef hgk => K.regularSliceGraph_segment_inter A hreg hef hgk)
  refine ⟨n, P, fun C => ⟨(hP C).1, (hP C).2.1⟩, ?_, hdisj⟩
  exact (K.regularSliceGraph_carrier A hreg hpure).trans hcover

end Geometry.SimplicialComplex
