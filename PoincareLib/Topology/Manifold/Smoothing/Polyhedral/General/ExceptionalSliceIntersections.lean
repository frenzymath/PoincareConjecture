import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.ExceptionalSliceSegments
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.SimplexExtremeFaces
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.ExtremeSegmentIntersections

/-!
# Simplicial incidence of exceptional section edges

Each realized graph edge is an exact original triangle section.
The extreme common-face argument supplies the full simplicial
intersection law, also at the distinguished zero vertex.
See Alexander 1924, p. 6 and M76 derivation 150.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- Two realized exceptional section edges meet only in the
convex hull of their common endpoints. See Alexander p. 6 and
M76 derivation 150. -/
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
