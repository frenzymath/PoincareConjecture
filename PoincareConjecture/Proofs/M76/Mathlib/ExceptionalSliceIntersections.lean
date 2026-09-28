import PoincareConjecture.Proofs.M76.Mathlib.ExceptionalSliceSegments
import PoincareConjecture.Proofs.M76.Mathlib.SimplexExtremeFaces
import PoincareConjecture.Proofs.M76.Mathlib.ExtremeSegmentIntersections










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]




theorem exceptionalSliceGraph_segment_inter (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hAq : A q = 0)
    {a b c d : Option (K.strictCrossingEdges A)}
    (hab : (K.exceptionalSliceGraph A q).Adj a b)
    (hcd : (K.exceptionalSliceGraph A q).Adj c d) :
    segment ℝ (K.exceptionalCrossingPoint A q a) (K.exceptionalCrossingPoint A q b) ∩
      segment ℝ (K.exceptionalCrossingPoint A q c) (K.exceptionalCrossingPoint A q d) ⊆
        convexHull ℝ (({K.exceptionalCrossingPoint A q a,
          K.exceptionalCrossingPoint A q b} : Set E) ∩
          {K.exceptionalCrossingPoint A q c, K.exceptionalCrossingPoint A q d}) := by
  obtain ⟨s, hs, _, hslice⟩ := K.exceptionalSliceGraph_segment A hAq hab
  obtain ⟨t, ht, _, htslice⟩ := K.exceptionalSliceGraph_segment A hAq hcd
  apply segment_inter_subset_convexHull_of_isExtreme
  · rw [hslice, htslice]
    exact K.isExtreme_convexHull_section_inter hs ht {x | A x = 0}
  · rw [hslice, htslice, inter_comm (convexHull ℝ (s : Set E) ∩ _)]
    exact K.isExtreme_convexHull_section_inter ht hs {x | A x = 0}

end Geometry.SimplicialComplex
