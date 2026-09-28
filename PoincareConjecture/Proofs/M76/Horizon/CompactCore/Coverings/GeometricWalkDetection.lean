import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Coverings.DetectedLoops
import PoincareConjecture.Proofs.M76.Mathlib.FiniteBarycentricCoordinates
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.GeometricWalkPaths

set_option autoImplicit false

namespace Geometry.SimplicialComplex

open StdSimplexCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] (K : SimplicialComplex ℝ E)
  [Fintype K.vertices]

theorem finiteBarycentricHomeomorph_vertex (u : K.vertices) :
    K.finiteBarycentricHomeomorph
      (K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricVertex u
        (K.vertexAbstractComplex.singleton_mem u)) =
      (⟨u, K.vertices_subset_space u.property⟩ : K.space) := by
  apply Subtype.ext
  exact barycentricMap_single _ u

theorem finiteBarycentricHomeomorph_edgePath {u v : K.vertices}
    (h : K.vertexAbstractComplex.edgeGraph.Adj u v) (t : unitInterval) :
    K.finiteBarycentricHomeomorph (K.vertexAbstractComplex.barycentricEdgePath h t) =
      K.geometricEdgePath h t := by
  apply Subtype.ext
  change barycentricMap ((↑) : K.vertices → E)
      (AffineMap.lineMap (Pi.single u 1 : K.vertices → ℝ)
        (Pi.single v 1 : K.vertices → ℝ) (t : ℝ)) =
    AffineMap.lineMap (u : E) (v : E) (t : ℝ)
  simp [AffineMap.lineMap_apply, barycentricMap_single]

theorem finiteBarycentricHomeomorph_walkPath {u v : K.vertices}
    (w : K.vertexAbstractComplex.edgeGraph.Walk u v) (t : unitInterval) :
    K.finiteBarycentricHomeomorph (K.vertexAbstractComplex.barycentricWalkPath w t) =
      K.geometricWalkPath w t := by
  induction w generalizing t with
  | nil => exact K.finiteBarycentricHomeomorph_vertex _
  | cons h w ih =>
    change K.finiteBarycentricHomeomorph
        (((K.vertexAbstractComplex.barycentricEdgePath h).trans
          (K.vertexAbstractComplex.barycentricWalkPath w)) t) =
      ((K.geometricEdgePath h).trans (K.geometricWalkPath w)) t
    simp only [Path.trans_apply]
    split_ifs
    · exact K.finiteBarycentricHomeomorph_edgePath h _
    · exact ih _

theorem geometricWalk_not_homotopic_refl_of_value_ne_zero
    (c : K.vertexAbstractComplex.toPreAbstractSimplicialComplex.ModTwoEdgeCocycle)
    {u : K.vertices} (w : K.vertexAbstractComplex.edgeGraph.Walk u u)
    (hw : c.walkValue w ≠ 0) :
    ¬(K.geometricWalkPath w).Homotopic (Path.refl _) := by
  rintro ⟨H⟩
  apply K.vertexAbstractComplex.barycentricWalk_not_homotopic_refl_of_value_ne_zero c w hw
  have hwalk (t : unitInterval) : K.finiteBarycentricHomeomorph.symm
      (K.geometricWalkPath w t) = K.vertexAbstractComplex.barycentricWalkPath w t := by
    rw [← K.finiteBarycentricHomeomorph_walkPath w t]
    exact K.finiteBarycentricHomeomorph.symm_apply_apply _
  have hv : K.finiteBarycentricHomeomorph.symm
      (⟨u, K.vertices_subset_space u.property⟩ : K.space) =
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricVertex u
        (K.vertexAbstractComplex.singleton_mem u) := by
    rw [← K.finiteBarycentricHomeomorph_vertex u]
    exact K.finiteBarycentricHomeomorph.symm_apply_apply _
  refine ⟨{
    toFun := fun z => K.finiteBarycentricHomeomorph.symm (H z)
    continuous_toFun := K.finiteBarycentricHomeomorph.symm.continuous.comp H.continuous
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    exact (congrArg K.finiteBarycentricHomeomorph.symm (H.map_zero_left t)).trans (hwalk t)
  · intro t
    exact (congrArg K.finiteBarycentricHomeomorph.symm (H.map_one_left t)).trans hv
  · intro t x hx
    exact (congrArg K.finiteBarycentricHomeomorph.symm (H.prop t x hx)).trans (hwalk x)

end Geometry.SimplicialComplex
