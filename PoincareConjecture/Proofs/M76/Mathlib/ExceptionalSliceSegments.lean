import PoincareConjecture.Proofs.M76.Mathlib.ExceptionalSliceGraph
import PoincareConjecture.Proofs.M76.Mathlib.ExceptionalTriangleSlice
import PoincareConjecture.Proofs.M76.Mathlib.RegularTriangleIntersection

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

theorem exceptionalSliceGraph_segment (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hAq : A q = 0)
    {a b : Option (K.strictCrossingEdges A)} (hab : (K.exceptionalSliceGraph A q).Adj a b) :
    ∃ t ∈ K.faces, t.card = 3 ∧
      segment ℝ (K.exceptionalCrossingPoint A q a) (K.exceptionalCrossingPoint A q b) =
        convexHull ℝ (t : Set E) ∩ {x | A x = 0} := by
  have hnone (e : K.strictCrossingEdges A) :
      segment ℝ q (A.straddlingPoint e.val e.property.2) =
        convexHull ℝ (↑(insert q e.val) : Set E) ∩ {x | A x = 0} := by
    have hcopy := e.property.2
    obtain ⟨u, v, hu, hv, heq⟩ := hcopy
    rw [A.straddlingPoint_eq_zeroCrossing e.property.2 hu hv heq,
      Finset.coe_insert, heq]
    exact (A.convexHull_zero_apex_pair_inter_zero hAq hu hv).symm
  cases a with
  | none =>
    cases b with
    | none => exact hab.elim
    | some e => exact ⟨insert q e.val, hab.1, hab.2, hnone e⟩
  | some e =>
    cases b with
    | none =>
      exact ⟨insert q e.val, hab.1, hab.2, (segment_symm ℝ _ _).trans (hnone e)⟩
    | some f =>
      obtain ⟨hne, t, ht, hcard, het, hft⟩ := hab
      have hef : e.val ≠ f.val := fun h => hne (Subtype.ext h)
      have hunion : e.val ∪ f.val = t := Finset.union_eq_triangle
        (AffineMap.StraddlesZero.card A e.property.2)
        (AffineMap.StraddlesZero.card A f.property.2) hcard het hft hef
      have hreg : ∀ v ∈ t, A v ≠ 0 := by
        intro v hv
        rw [← hunion] at hv
        rcases Finset.mem_union.mp hv with he | hf
        · exact e.property.2.ne_zero he
        · exact f.property.2.ne_zero hf
      exact ⟨t, ht, hcard, A.segment_straddlingPoints_eq_triangleSlice
        e.property.2 f.property.2 hcard hreg het hft hef⟩

end Geometry.SimplicialComplex
