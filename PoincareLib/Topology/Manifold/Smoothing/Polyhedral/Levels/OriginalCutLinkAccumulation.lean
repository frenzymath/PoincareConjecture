import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.OriginalCutLinkZeroSection
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.CentralLinkSigns

/-!
# The same original cut on an auxiliary signed link

The unchanged polygon section determines its complete link
zero pair. Actual carrier sign accumulations give both strict
link signs without requiring generic auxiliary vertex heights.
See Alexander 1924, pp. 6--8, Cairns 1940, pp. 801--802
and M76 derivation 286au.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {n : ℕ}

/-- The literal original cut gives exact zero data and both
strict signs on any finite vertex link with the same carrier
section and actual central height accumulations. Auxiliary
vertices of equal height are allowed. See Alexander pp. 6--8
and M76 derivation 286au. -/
theorem original_cut_link_data_of_surface_accumulation
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hzero : (0 : E) ∈ K.vertices) (A : E →ₗ[ℝ] ℝ)
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P)
    (hsection : P.boundary ℝ = K.space ∩ {x | A x = 0})
    (t : Fin (n + 3) → ℝ) (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1)
    (i : Fin (n + 3)) (hvertex : P (finRotate (n + 3) i) = 0)
    (hpos : (0 : E) ∈ closure (K.space ∩ {x | 0 < A x}))
    (hneg : (0 : E) ∈ closure (K.space ∩ {x | A x < 0})) :
    (NormedSpace.normalize '' ((K.link 0).space ∩ {x | A x = 0}) =
      {NormedSpace.normalize (P.edgeCut t i),
        NormedSpace.normalize (P.edgeCut t (finRotate (n + 3) i))}) ∧
      ((K.link 0).space ∩ {x | A x = 0}).ncard = 2 ∧
      (∃ x ∈ (K.link 0).space, A x < 0) ∧
      ∃ x ∈ (K.link 0).space, 0 < A x := by
  obtain ⟨hpair, hcard⟩ := K.original_cut_link_zero_data hK hzero A
    P hP hinj hsection t ht i hvertex
  obtain ⟨hpositive, hnegative⟩ :=
    K.exists_both_link_signs_of_surface_accumulation hK hzero A hpos hneg
  exact ⟨hpair, hcard, hnegative, hpositive⟩

end Geometry.SimplicialComplex
