import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicRegularSection

set_option autoImplicit false

open Set

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Subsingleton.hasAlexanderCurvePresentation {s : Set E} (hs : s.Subsingleton) :
    HasAlexanderCurvePresentation s 0 := by
  apply hasAlexanderCurvePresentation_zero_of_disjoint_family
    (fun i : Empty => i.elim) (fun i : Empty => i.elim)
    (fun i => i.elim) (fun i => i.elim) hs
  simp only [iUnion_of_empty, union_empty]

end Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem hasDisjointPolygonPresentation (P : Polygon E (n + 3))
    (hinj : Function.Injective P) (hP : P.HasSimplicialEdges) :
    HasDisjointPolygonPresentation (P.boundary ℝ) := by
  apply hasDisjointPolygonPresentation_of_family (fun _ : Unit => n) (fun _ => P)
    (fun _ => ⟨hinj, hP⟩)
  · simp only [iUnion_const]
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

theorem hasAlexanderCurvePresentation (P : Polygon E (n + 3))
    (hinj : Function.Injective P) (hP : P.HasSimplicialEdges) :
    HasAlexanderCurvePresentation (P.boundary ℝ) 0 :=
  (P.hasDisjointPolygonPresentation hinj hP).hasAlexanderCurvePresentation

end Polygon
