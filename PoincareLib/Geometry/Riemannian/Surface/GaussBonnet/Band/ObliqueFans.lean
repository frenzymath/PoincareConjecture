import PoincareLib.Geometry.Riemannian.Surface.GaussBonnet.Band.ObliqueCorners
import PoincareLib.Topology.Surface.Triangulation.Faces.Bands.ObliqueFrontier

/-!
# Complete metric contribution at an internal bottom cut

Every constituent triangle corner is located at a retained band vertex.
Injectivity of those geometric vertices makes the full weighted corner sum
reduce to the three actual corners in the bottom half-fan.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Classical
open scoped Manifold ContDiff Bundle Matrix
open Poincare.Topology.Plane.Triangles Poincare.Topology.Plane.Curves

namespace PoincareMT.Topology.Surface.ObliqueBandFaces

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

/-- The retained band vertex belonging to an actual face corner. -/
def cornerVertexIndex (p : Fin B.interface.count × Bool) (k : Fin 3) :
    Fin (B.interface.count + 1) × Bool :=
  if k = 0 then (p.1.castSucc, false)
  else if k = 1 then
    if p.2 then (p.1.castSucc, true) else (p.1.succ, false)
  else (p.1.succ, true)

private theorem faceCoordinates_apply (p : Fin B.interface.count × Bool)
    (z : EuclideanSpace ℝ (Fin 2)) :
    B.faceCoordinates p z = B.coordinates (collarParameterEquiv.symm
      (graphStripMap (fun _ => 0) (B.upperGraph p.1) (collarParameterEquiv z))) := rfl

/-- The face-to-vertex indexing agrees with the actual coordinate maps. -/
theorem face_corner_eq_vertex (p : Fin B.interface.count × Bool) (k : Fin 3) :
    B.faceCoordinates p (B.faceBasis p k) = B.vertex (B.cornerVertexIndex p k) := by
  rcases p with ⟨i, s⟩
  rw [B.faceCoordinates_apply]
  cases s <;> fin_cases k
  all_goals
    simp [cornerVertexIndex, faceBasis, SmoothGraphBandPair.faceBasis,
      vertex, graphStripMap, collarParameterEquiv,
      (B.upperGraph_endpoints i).1, (B.upperGraph_endpoints i).2]

private theorem vertex_parameter_mem_source (p : Fin (B.interface.count + 1) × Bool) :
    collarParameterEquiv.symm (B.cut p.1, if p.2 then B.interface.height p.1 else 0) ∈
      B.coordinates.source := by
  obtain ⟨i, hi⟩ : ∃ i : Fin B.interface.count, p.1 = i.castSucc ∨ p.1 = i.succ := by
    by_cases h : (p.1 : ℕ) < B.interface.count
    · exact ⟨⟨p.1, h⟩, Or.inl (Fin.ext rfl)⟩
    · refine ⟨B.lastCell, Or.inr (Fin.ext ?_)⟩
      have hn := B.interface.count_pos
      have hp := p.1.isLt
      simp only [lastCell, Fin.val_succ]
      omega
  have ht : B.cut p.1 ∈ Icc (B.cut i.castSucc) (B.cut i.succ) := by
    rcases hi with hi | hi
    · rw [hi]
      exact left_mem_Icc.mpr (B.cut_strictMono Fin.castSucc_lt_succ).le
    · rw [hi]
      exact right_mem_Icc.mpr (B.cut_strictMono Fin.castSucc_lt_succ).le
  have hh : B.upperGraph i (B.cut p.1) = B.interface.height p.1 := by
    rcases hi with hi | hi
    · rw [hi]
      exact (B.upperGraph_endpoints i).1
    · rw [hi]
      exact (B.upperGraph_endpoints i).2
  apply (B.pair i).band_subset_source
  change (collarParameterEquiv (collarParameterEquiv.symm
      (B.cut p.1, if p.2 then B.interface.height p.1 else 0))).1 ∈
      Icc (B.cut i.castSucc) (B.cut i.succ) ∧ _
  rw [collarParameterEquiv.apply_symm_apply]
  refine ⟨ht, ?_⟩
  have hpos := (B.interface.vertex_height_bounds p.1).1
  change 0 ≤ (if p.2 then B.interface.height p.1 else 0) ∧
    (if p.2 then B.interface.height p.1 else 0) ≤ B.upperGraph i (B.cut p.1)
  rw [hh]
  cases p.2 <;> simp [hpos.le]

/-- Strict cut order, positive top height, and coordinate injectivity make
all retained geometric band vertices distinct. -/
theorem vertex_injective : Function.Injective B.vertex := by
  rintro ⟨i, s⟩ ⟨j, t⟩ h
  have hp := collarParameterEquiv.symm.injective
    (B.coordinates.injOn (B.vertex_parameter_mem_source (i, s))
      (B.vertex_parameter_mem_source (j, t)) h)
  have hij : i = j := B.cut_strictMono.injective (congrArg Prod.fst hp)
  subst j
  have hs := congrArg Prod.snd hp
  have hpos := (B.interface.vertex_height_bounds i).1
  cases s <;> cases t <;> simp_all

/-- A face corner lies at a retained band vertex exactly when its constructed
vertex index is that vertex; no other geometric coincidence is possible. -/
theorem face_corner_eq_vertex_iff (p : Fin B.interface.count × Bool) (k : Fin 3)
    (v : Fin (B.interface.count + 1) × Bool) :
    B.faceCoordinates p (B.faceBasis p k) = B.vertex v ↔ B.cornerVertexIndex p k = v := by
  rw [B.face_corner_eq_vertex, B.vertex_injective.eq_iff]

/-- Exactly the three adjacent bottom corners contribute to any weighted
sum over all actual band faces and all their corners. -/
theorem sum_corner_weights_internal_bottom
    (w : (Fin B.interface.count × Bool) → Fin 3 → ℝ)
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc) :
    (∑ p : Fin B.interface.count × Bool, ∑ k : Fin 3,
      if B.faceCoordinates p (B.faceBasis p k) = B.vertex (i.succ, false)
      then w p k else 0) = w (i, false) 1 + w (j, false) 0 + w (j, true) 0 := by
  classical
  have hstart (m : Fin B.interface.count) : m.castSucc = i.succ ↔ m = j := by
    rw [hij]
    exact Fin.castSucc_inj
  simp_rw [B.face_corner_eq_vertex_iff]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three,
    cornerVertexIndex]
  simp only [Fin.reduceEq, if_true, if_false, Bool.false_eq_true, Prod.mk.injEq,
    and_true, and_false, Bool.true_eq_false, hstart, Fin.succ_inj, add_zero]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- The complete pointwise metric corner contribution of an oblique band
at an internal bottom cut is `pi`; all other face corners are excluded by
the actual coordinate geometry and strict cut order. -/
theorem internal_bottom_vertex_fan (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc) :
    (∑ p : Fin B.interface.count × Bool, ∑ k : Fin 3,
      if B.faceCoordinates p (B.faceBasis p k) = B.vertex (i.succ, false)
      then coordinateTriangleAngle g (B.faceCoordinates p) (B.faceBasis p) k else 0) =
      Real.pi := by
  rw [B.sum_corner_weights_internal_bottom
    (fun p k => coordinateTriangleAngle g (B.faceCoordinates p) (B.faceBasis p) k) i j hij]
  exact B.internal_bottom_corner_fan hF hFi g i j hij

end PoincareMT.Topology.Surface.ObliqueBandFaces
