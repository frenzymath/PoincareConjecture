import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic









set_option autoImplicit false

namespace Geometry.SimplicialComplex

theorem exists_actual_edge_endpoints
    {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) :
    ∃ (a b : {s : K.faces // s.val.card = 2} → K.vertices),
      (∀ k, (a k : E) ≠ b k) ∧
      (∀ k, ({(a k : E), (b k : E)} : Finset E) = k.val.val) ∧
      Function.Injective (fun k => ({(a k : E), (b k : E)} : Finset E)) := by
  classical
  choose x y hxy hface using fun k : {s : K.faces // s.val.card = 2} =>
    Finset.card_eq_two.mp k.property
  have hx (k : {s : K.faces // s.val.card = 2}) : x k ∈ K.vertices := by
    apply K.down_closed k.val.property (Finset.singleton_subset_iff.mpr ?_)
      (Finset.singleton_nonempty _)
    rw [hface k]
    simp
  have hy (k : {s : K.faces // s.val.card = 2}) : y k ∈ K.vertices := by
    apply K.down_closed k.val.property (Finset.singleton_subset_iff.mpr ?_)
      (Finset.singleton_nonempty _)
    rw [hface k]
    simp
  refine ⟨fun k => ⟨x k, hx k⟩, fun k => ⟨y k, hy k⟩, hxy,
    fun k => (hface k).symm, ?_⟩
  intro i j hij
  apply Subtype.ext
  apply Subtype.ext
  exact (hface i).trans (hij.trans (hface j).symm)

end Geometry.SimplicialComplex
