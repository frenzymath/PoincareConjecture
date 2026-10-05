import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coverings.ClosedStarProjectionCoverage
import Mathlib.Analysis.Convex.Intrinsic

/-!
# The whole original face collection of an edge-chain carrier

An intrinsic-interior point of a face belongs to one of the
covering edge hulls. The original simplicial intersection law
then puts that whole face inside the covering edge. See Wall013,
section 3, and Hudson 1969, pp. 9--10.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

/-- When original edges cover the whole carrier, every original
face is a nonempty subface of one of those exact edges. This
recognizes the entire face collection, with no replacement complex
or ambient dimension bound. See Wall013, section 3. -/
theorem faces_of_edge_chain_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) {n : ℕ} (p : Fin (n + 2) → E)
    (hedge : ∀ i : Fin (n + 1), {p i.castSucc, p i.succ} ∈ K.faces)
    (hcover : K.space = ⋃ i : Fin (n + 1), segment ℝ (p i.castSucc) (p i.succ))
    (s : Finset E) :
    s ∈ K.faces ↔ s.Nonempty ∧ ∃ i : Fin (n + 1), s ⊆ {p i.castSucc, p i.succ} := by
  constructor
  · intro hs
    have hne := K.nonempty_of_mem_faces hs
    obtain ⟨x, hx⟩ := (intrinsicInterior_nonempty (convex_convexHull ℝ (s : Set E))).mpr
      (convexHull_nonempty_iff.mpr hne.to_set)
    have hxK := K.convexHull_subset_space hs (intrinsicInterior_subset hx)
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.subset hxK)
    refine ⟨hne, i, K.subset_of_mem_intrinsicInterior_face hs (hedge i) hx ?_⟩
    simpa only [Finset.coe_pair, convexHull_pair] using hi
  · rintro ⟨hne, i, hsi⟩
    exact K.down_closed (hedge i) hsi hne

end Geometry.SimplicialComplex
