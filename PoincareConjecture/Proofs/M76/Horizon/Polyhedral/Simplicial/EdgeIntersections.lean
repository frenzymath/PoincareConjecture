import Mathlib.Analysis.Convex.SimplicialComplex.Basic










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [DecidableEq E]



theorem segment_inter_segment_of_distinct_edges (K : SimplicialComplex 𝕜 E)
    {a b c d : E} (hab : {a, b} ∈ K.faces) (hcd : {c, d} ∈ K.faces)
    (hne : ({a, b} : Finset E) ≠ {c, d}) :
    segment 𝕜 a b ∩ segment 𝕜 c d = ({a, b} : Set E) ∩ {c, d} := by
  have hsub : (({a, b} : Set E) ∩ {c, d}).Subsingleton := by
    intro u hu v hv
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff] at hu hv
    rcases hu with ⟨hua | hub, huc | hud⟩ <;>
      rcases hv with ⟨hva | hvb, hvc | hvd⟩ <;>
      subst_vars <;> simp_all [Finset.pair_comm]
  have heq := K.convexHull_inter_convexHull hab hcd
  simp only [Finset.coe_pair, convexHull_pair] at heq
  exact heq.trans hsub.convex.convexHull_eq



theorem mem_segment_inter_of_distinct_edges (K : SimplicialComplex 𝕜 E)
    {a b c d x : E} (hab : {a, b} ∈ K.faces) (hcd : {c, d} ∈ K.faces)
    (hne : ({a, b} : Finset E) ≠ {c, d})
    (hx : x ∈ segment 𝕜 a b ∩ segment 𝕜 c d) :
    (x = a ∨ x = b) ∧ (x = c ∨ x = d) := by
  rw [K.segment_inter_segment_of_distinct_edges hab hcd hne] at hx
  exact hx

end Geometry.SimplicialComplex
