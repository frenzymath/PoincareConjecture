import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegions
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialPolygon









set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} {m n : ℕ}




def reindex (P : Polygon E n) (e : Fin m ≃ Fin n) : Polygon E m := ⟨P ∘ e⟩

variable [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem edgeSet_reindex (P : Polygon E n) (e : Fin m ≃ Fin n)
    (he : ∀ i, e (finRotate m i) = finRotate n (e i)) (i : Fin m) :
    (P.reindex e).edgeSet ℝ i = P.edgeSet ℝ (e i) := by
  change affineSegment ℝ (P (e i)) (P (e (finRotate m i))) = _
  rw [he]
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in


theorem edgeVertices_reindex (P : Polygon E n) (e : Fin m ≃ Fin n)
    (he : ∀ i, e (finRotate m i) = finRotate n (e i)) (i : Fin m) :
    (P.reindex e).edgeVertices i = P.edgeVertices (e i) := by
  classical
  simp only [edgeVertices, reindex, Function.comp_apply, he]



theorem boundary_reindex (P : Polygon E n) (e : Fin m ≃ Fin n)
    (he : ∀ i, e (finRotate m i) = finRotate n (e i)) :
    (P.reindex e).boundary ℝ = P.boundary ℝ := by
  simp only [boundary, P.edgeSet_reindex e he]
  exact e.surjective.iUnion_comp _



theorem hasSimplicialEdges_reindex (P : Polygon E n) (hP : P.HasSimplicialEdges)
    (e : Fin m ≃ Fin n) (he : ∀ i, e (finRotate m i) = finRotate n (e i)) :
    (P.reindex e).HasSimplicialEdges := by
  intro i j
  simpa only [P.edgeSet_reindex e he, P.edgeVertices_reindex e he] using hP (e i) (e j)



theorem inside_reindex (P : Polygon E n) (e : Fin m ≃ Fin n)
    (he : ∀ i, e (finRotate m i) = finRotate n (e i)) :
    (P.reindex e).inside = P.inside := by
  simp only [inside, P.boundary_reindex e he]

end Polygon
