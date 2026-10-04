import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.IntrinsicRegularSection

/-!
# Complete zero-charge presentations of singleton and polygon sections

The empty polygon family represents a subsingleton section;
one polygon represents its full regular boundary. These
are the actual generic sweep's extreme and intermediate
levels. See Alexander 1924, pp. 6--8 and derivation 281.
-/

set_option autoImplicit false

open Set

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An empty or singleton section has a zero-charge complete
presentation with no polygons. See M76 derivation 281. -/
theorem Subsingleton.hasAlexanderCurvePresentation {s : Set E} (hs : s.Subsingleton) :
    HasAlexanderCurvePresentation s 0 := by
  apply hasAlexanderCurvePresentation_zero_of_disjoint_family
    (fun i : Empty => i.elim) (fun i : Empty => i.elim)
    (fun i => i.elim) (fun i => i.elim) hs
  simp only [iUnion_of_empty, union_empty]

end Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- One simple polygon is its complete one-member disjoint
polygon presentation. See M76 derivation 281. -/
theorem hasDisjointPolygonPresentation (P : Polygon E (n + 3))
    (hinj : Function.Injective P) (hP : P.HasSimplicialEdges) :
    HasDisjointPolygonPresentation (P.boundary ℝ) := by
  apply hasDisjointPolygonPresentation_of_family (fun _ : Unit => n) (fun _ => P)
    (fun _ => ⟨hinj, hP⟩)
  · simp only [iUnion_const]
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

/-- A complete single-polygon section has zero Alexander
charge. See Alexander pp. 6--8 and M76 derivation 281. -/
theorem hasAlexanderCurvePresentation (P : Polygon E (n + 3))
    (hinj : Function.Injective P) (hP : P.HasSimplicialEdges) :
    HasAlexanderCurvePresentation (P.boundary ℝ) 0 :=
  (P.hasDisjointPolygonPresentation hinj hP).hasAlexanderCurvePresentation

end Polygon
