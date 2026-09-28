import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.EndpointSectorGerms
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.CutGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

theorem mem_chart_image_iff_mem_linearGraphCoordinates_image
    {M : Type*} [TopologicalSpace M]
    (C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ)) (A : Set M)
    (z : EuclideanSpace ℝ (Fin 2)) :
    z ∈ C.symm '' A ↔ collarParameterEquiv.symm (L z) ∈ (linearGraphCoordinates C L).symm '' A := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, ?_⟩
    exact L.injective (collarParameterEquiv.symm.injective h)

namespace FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M} {a b : ℝ}
  {G : D.OrientedGraphPiece e R C a b} {ua wa ub wb : ℝ}
  {P : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb}
  {δ ra rb : ℝ} (B : G.FixedStripBandFaces P δ ra rb)

noncomputable def ambientEndpointCut (right : Bool) : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ :=
  (B.faces.endpointCutFunctional right).comp
    (G.frame.trans collarParameterEquiv.symm).toContinuousLinearMap.toLinearMap.toAffineMap

noncomputable def ambientEndpointTop (right : Bool) : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ :=
  (B.faces.topLineFunctional (if right then B.faces.lastCell else B.faces.firstCell)).comp
    (G.frame.trans collarParameterEquiv.symm).toContinuousLinearMap.toLinearMap.toAffineMap

theorem ambientEndpointCut_linear_apply (right : Bool) (v : EuclideanSpace ℝ (Fin 2)) :
    (B.ambientEndpointCut right).linear v =
      if right then wb * (G.frame v).1 - ub * (G.frame v).2
      else -(wa * (G.frame v).1 - ua * (G.frame v).2) := by
  cases right <;> simp [ambientEndpointCut, ObliqueBandFaces.endpointCutFunctional,
    transverseCutLine]

theorem ambientEndpointCut_first_base (hab : a ≤ b) :
    B.ambientEndpointCut false (C.symm ((D.edge e.1 e.2).map a)) = 0 := by
  have hbase := G.graph_coordinates a (G.interval_source (left_mem_Icc.mpr hab))
  change -(wa * ((G.frame (C.symm ((D.edge e.1 e.2).map a))).1 - G.parameter a) -
    ua * ((G.frame (C.symm ((D.edge e.1 e.2).map a))).2 - G.lower (G.parameter a))) = 0
  rw [hbase]
  simp

theorem ambientEndpointCut_last_base (hab : a ≤ b) :
    B.ambientEndpointCut true (C.symm ((D.edge e.1 e.2).map b)) = 0 := by
  have hbase := G.graph_coordinates b (G.interval_source (right_mem_Icc.mpr hab))
  change wb * ((G.frame (C.symm ((D.edge e.1 e.2).map b))).1 - G.parameter b) -
    ub * ((G.frame (C.symm ((D.edge e.1 e.2).map b))).2 - G.lower (G.parameter b)) = 0
  rw [hbase]
  simp

theorem ambient_first_vertex (hab : a ≤ b) :
    collarParameterEquiv.symm (G.frame
      (C.symm ((D.edge e.1 e.2).map a) + ra • G.frame.symm (ua, wa))) = B.faces.planarTopVertex 0 := by
  have hbase := G.graph_coordinates a (G.interval_source (left_mem_Icc.mpr hab))
  apply collarParameterEquiv.injective
  rw [collarParameterEquiv.apply_symm_apply]
  change G.frame (C.symm ((D.edge e.1 e.2).map a) + ra • G.frame.symm (ua, wa)) =
    (B.faces.interface.cut 0,
      G.lower (B.faces.interface.cut 0) + B.faces.interface.height 0)
  rw [B.faces.interface.first_vertex, map_add, map_smul, G.frame.apply_symm_apply, hbase]
  ext <;> simp [smul_eq_mul]

theorem ambient_last_vertex (hab : a ≤ b) :
    collarParameterEquiv.symm (G.frame
      (C.symm ((D.edge e.1 e.2).map b) + rb • G.frame.symm (ub, wb))) =
        B.faces.planarTopVertex (Fin.last B.faces.interface.count) := by
  have hbase := G.graph_coordinates b (G.interval_source (right_mem_Icc.mpr hab))
  apply collarParameterEquiv.injective
  rw [collarParameterEquiv.apply_symm_apply]
  change G.frame (C.symm ((D.edge e.1 e.2).map b) + rb • G.frame.symm (ub, wb)) =
    (B.faces.interface.cut (Fin.last B.faces.interface.count),
      G.lower (B.faces.interface.cut (Fin.last B.faces.interface.count)) +
        B.faces.interface.height (Fin.last B.faces.interface.count))
  rw [B.faces.interface.last_vertex, map_add, map_smul, G.frame.apply_symm_apply, hbase]
  ext <;> simp [smul_eq_mul]

theorem ambient_carrier_first_top_eventually_iff (hab : a ≤ b) :
    ∀ᶠ z in 𝓝 (C.symm ((D.edge e.1 e.2).map a) + ra • G.frame.symm (ua, wa)),
      z ∈ C.symm '' B.faces.carrier ↔
        B.ambientEndpointCut false z ≤ 0 ∧ B.ambientEndpointTop false z ≤ 0 := by
  have hc : ContinuousAt (fun z => collarParameterEquiv.symm (G.frame z))
      (C.symm ((D.edge e.1 e.2).map a) + ra • G.frame.symm (ua, wa)) :=
    (collarParameterEquiv.symm.continuous.comp G.frame.continuous).continuousAt
  have hlocal := hc.eventually (by
    simpa only [B.ambient_first_vertex hab] using B.faces.planar_carrier_first_top_eventually_iff)
  filter_upwards [hlocal] with z hz
  rw [mem_chart_image_iff_mem_linearGraphCoordinates_image C G.frame B.faces.carrier]
  exact hz

theorem ambient_carrier_last_top_eventually_iff (hab : a ≤ b) :
    ∀ᶠ z in 𝓝 (C.symm ((D.edge e.1 e.2).map b) + rb • G.frame.symm (ub, wb)),
      z ∈ C.symm '' B.faces.carrier ↔
        B.ambientEndpointCut true z ≤ 0 ∧ B.ambientEndpointTop true z ≤ 0 := by
  have hc : ContinuousAt (fun z => collarParameterEquiv.symm (G.frame z))
      (C.symm ((D.edge e.1 e.2).map b) + rb • G.frame.symm (ub, wb)) :=
    (collarParameterEquiv.symm.continuous.comp G.frame.continuous).continuousAt
  have hlocal := hc.eventually (by
    simpa only [B.ambient_last_vertex hab] using B.faces.planar_carrier_last_top_eventually_iff)
  filter_upwards [hlocal] with z hz
  rw [mem_chart_image_iff_mem_linearGraphCoordinates_image C G.frame B.faces.carrier]
  exact hz

end FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

namespace FiniteChartRegionDecomposition.OrientedEdgeGraphSubdivision.CutChain

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M} {a b : ℝ}
  {S : D.OrientedEdgeGraphSubdivision e R C a b}
  {dLeft dRight : EuclideanSpace ℝ (Fin 2)} (K : S.CutChain dLeft dRight)
  {δ r : ℝ}
  (B : ∀ i : Fin S.count, (S.piece i).FixedStripBandFaces (K.graphCuts i) δ r r)

private theorem linear_functional_eq_first_coordinate
    (L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ))
    (f : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ) (hf : f (L.symm (0, 1)) = 0)
    (v : EuclideanSpace ℝ (Fin 2)) :
    f v = (L v).1 * f (L.symm (1, 0)) := by
  have hv : v = (L v).1 • L.symm (1, 0) + (L v).2 • L.symm (0, 1) := by
    apply L.injective
    simp only [map_add, map_smul, L.apply_symm_apply]
    ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, hf, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]

theorem adjacent_cut_functionals_opposite
    (i j : Fin S.count) (hij : i.succ = j.castSucc) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : EuclideanSpace ℝ (Fin 2),
      (B j).ambientEndpointCut false z = -c * (B i).ambientEndpointCut true z := by
  let L := (S.piece i).frame
  let d := K.direction i.succ
  let v := (S.piece j).frame.symm
    (1, deriv (S.piece j).lower ((S.piece j).parameter (S.cut i.succ)))
  let f := ((B j).ambientEndpointCut false).linear
  let e₁ := L.symm (1, 0)
  have hd : d = L.symm (0, 1) := K.internal_direction i j hij
  have hdir : (S.piece j).frame (K.direction j.castSucc) = (S.piece j).frame d :=
    congrArg (S.piece j).frame (congrArg K.direction hij.symm)
  have hfd : f (L.symm (0, 1)) = 0 := by
    rw [← hd]
    dsimp only [f]
    rw [(B j).ambientEndpointCut_linear_apply]
    simp only [Bool.false_eq_true, ↓reduceIte, hdir]
    ring
  have hsep : (K.separator i j hij) (L.symm (0, 1)) = 0 := by
    rw [← hd]
    exact K.separator_zero i j hij
  have hse : 0 < (K.separator i j hij) e₁ := by
    have hp := K.separator_left_pos i j hij
    change 0 < (K.separator i j hij).toLinearMap
      ((S.piece i).frame.symm (1, deriv (S.piece i).lower ((S.piece i).parameter (S.cut i.succ)))) at hp
    rw [linear_functional_eq_first_coordinate L (K.separator i j hij).toLinearMap hsep] at hp
    simp only [L, ContinuousLinearEquiv.apply_symm_apply, one_mul] at hp
    exact hp
  have hvx : 0 < (L v).1 := by
    have hp := K.separator_right_pos i j hij
    change 0 < (K.separator i j hij).toLinearMap v at hp
    rw [linear_functional_eq_first_coordinate L (K.separator i j hij).toLinearMap hsep] at hp
    exact (mul_pos_iff_of_pos_right hse).mp hp
  have hfv : f v < 0 := by
    have hp := K.left_transverse j
    have hcut : deriv (S.piece j).lower ((S.piece j).parameter (S.cut j.castSucc)) =
        deriv (S.piece j).lower ((S.piece j).parameter (S.cut i.succ)) :=
      congrArg (fun x => deriv (S.piece j).lower ((S.piece j).parameter (S.cut x))) hij.symm
    rw [hcut] at hp
    dsimp only [f]
    rw [(B j).ambientEndpointCut_linear_apply]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [v]
    rw [(S.piece j).frame.apply_symm_apply]
    change -(((S.piece j).frame (K.direction j.castSucc)).2 * 1 -
      ((S.piece j).frame (K.direction j.castSucc)).1 *
        deriv (S.piece j).lower ((S.piece j).parameter (S.cut i.succ))) < 0
    nlinarith
  have hfe : f e₁ < 0 := by
    rw [linear_functional_eq_first_coordinate L f hfd v] at hfv
    by_contra hn
    have hh := mul_nonneg hvx.le (le_of_not_gt hn)
    exact (not_lt_of_ge hh) hfv
  refine ⟨-f e₁, neg_pos.mpr hfe, ?_⟩
  intro z
  let p := C.symm ((D.edge e.1 e.2).map (S.cut i.succ))
  have hip : (B i).ambientEndpointCut true p = 0 :=
    (B i).ambientEndpointCut_last_base (S.cut_lt i).le
  have hjp : (B j).ambientEndpointCut false p = 0 := by
    have h := (B j).ambientEndpointCut_first_base (S.cut_lt j).le
    have hp : C.symm ((D.edge e.1 e.2).map (S.cut j.castSucc)) = p := by dsimp [p]; rw [hij]
    rwa [hp] at h
  have hlin_i : ((B i).ambientEndpointCut true).linear (z - p) = (L (z - p)).1 := by
    rw [(B i).ambientEndpointCut_linear_apply]
    have hdi : L d = (0, 1) := by rw [hd, L.apply_symm_apply]
    change (L d).2 * (L (z - p)).1 - (L d).1 * (L (z - p)).2 = _
    rw [hdi]
    simp
  have hi := ((B i).ambientEndpointCut true).linearMap_vsub z p
  have hj := ((B j).ambientEndpointCut false).linearMap_vsub z p
  simp only [vsub_eq_sub, hip, hjp, sub_zero] at hi hj
  rw [← hj, ← hi, hlin_i]
  change f (z - p) = -(-f e₁) * (L (z - p)).1
  rw [linear_functional_eq_first_coordinate L f hfd, neg_neg]
  ring

theorem adjacent_top_carrier_eventually_iff_affine_sectors
    (i j : Fin S.count) (hij : i.succ = j.castSucc) :
    ∀ᶠ z in 𝓝 (C.symm ((D.edge e.1 e.2).map (S.cut i.succ)) + r • K.direction i.succ),
      z ∈ C.symm '' ((B i).faces.carrier ∪ (B j).faces.carrier) ↔
        ((B i).ambientEndpointCut true z ≤ 0 ∧ (B i).ambientEndpointTop true z ≤ 0) ∨
        ((B j).ambientEndpointCut false z ≤ 0 ∧ (B j).ambientEndpointTop false z ≤ 0) := by
  have hi := (B i).ambient_carrier_last_top_eventually_iff (S.cut_lt i).le
  have hj := (B j).ambient_carrier_first_top_eventually_iff (S.cut_lt j).le
  simp only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply] at hi hj
  have hpoint : C.symm ((D.edge e.1 e.2).map (S.cut j.castSucc)) + r • K.direction j.castSucc =
      C.symm ((D.edge e.1 e.2).map (S.cut i.succ)) + r • K.direction i.succ := by rw [hij]
  rw [hpoint] at hj
  filter_upwards [hi, hj] with z hiz hjz
  rw [image_union, mem_union, hiz, hjz]

theorem adjacent_top_carrier_eventually_iff_common_cut
    (i j : Fin S.count) (hij : i.succ = j.castSucc) :
    ∀ᶠ z in 𝓝 (C.symm ((D.edge e.1 e.2).map (S.cut i.succ)) + r • K.direction i.succ),
      z ∈ C.symm '' ((B i).faces.carrier ∪ (B j).faces.carrier) ↔
        ((B i).ambientEndpointCut true z ≤ 0 ∧ (B i).ambientEndpointTop true z ≤ 0) ∨
        (0 ≤ (B i).ambientEndpointCut true z ∧ (B j).ambientEndpointTop false z ≤ 0) := by
  obtain ⟨c, hc, heq⟩ := K.adjacent_cut_functionals_opposite B i j hij
  filter_upwards [K.adjacent_top_carrier_eventually_iff_affine_sectors B i j hij] with z hz
  rw [hz, heq z]
  have hsign : -c * (B i).ambientEndpointCut true z ≤ 0 ↔ 0 ≤ (B i).ambientEndpointCut true z := by
    constructor
    · intro h
      by_contra hn
      have hp := mul_neg_of_pos_of_neg hc (lt_of_not_ge hn)
      nlinarith
    · intro h
      have hp := mul_nonneg hc.le h
      nlinarith
  rw [hsign]

end FiniteChartRegionDecomposition.OrientedEdgeGraphSubdivision.CutChain

end PoincareConjecture.Topology.Surface
