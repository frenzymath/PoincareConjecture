


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.Sectors.Basic








set_option autoImplicit false
open Set Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))

theorem edge_mem_boundary (a : D.EdgeIndex) (t : ℝ) :
    (D.edge a.1 a.2).map t ∈ chartDiskBoundaryUnion D.centers D.radius := by
  rw [chartDiskBoundaryUnion_eq_iUnion_chartCircle D.centers D.radius
    D.radius_pos D.closedBall_subset_target]
  apply mem_iUnion₂.mpr
  refine ⟨a.1.1, a.1.1.property, D.edgeCurve a t, ?_, (D.edge_map_eq a t).symm⟩
  exact coordinateCircleArc_mem_sphere _ (D.radius_pos a.1.1 a.1.1.property).le _ _


noncomputable def edgeVertexGerm {p : M}
    (P : ChartCircleArrangementVertexPatch D.radius p) (a : D.EdgeIndex) (t₀ d t : ℝ) :
    ℝ × ℝ :=
  collarParameterEquiv (P.coordinates.symm ((D.edge a.1 a.2).map (t₀ + d * t))) - P.center



theorem exists_edgeVertexGerm_neighborhood {p : M}
    (P : ChartCircleArrangementVertexPatch D.radius p)
    (hlocal : ∀ q ∈ P.carrier,
      q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ P.circles)
    (a : D.EdgeIndex) {t₀ d : ℝ} (hd : d ≠ 0)
    (hp : (D.edge a.1 a.2).map t₀ = p) :
    ∃ U : Set ℝ, IsOpen U ∧ 0 ∈ U ∧
      ContDiffOn ℝ ∞ (D.edgeVertexGerm P a t₀ d) U ∧
      D.edgeVertexGerm P a t₀ d 0 = 0 ∧
      deriv (D.edgeVertexGerm P a t₀ d) 0 ≠ 0 ∧
      ∀ t ∈ U, (D.edgeVertexGerm P a t₀ d t).1 = 0 ∨
        (D.edgeVertexGerm P a t₀ d t).2 = 0 := by
  let η (t : ℝ) := (D.edge a.1 a.2).map (t₀ + d * t)
  have hη : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ η :=
    (D.edge_contMDiff a).comp
      ((contDiff_const.add (contDiff_const.mul contDiff_id)).contMDiff)
  let U := η ⁻¹' P.openCarrier
  have hU : IsOpen U := P.isOpen_openCarrier.preimage hη.continuous
  have hη0 : η 0 = p := by simpa [η] using hp
  have hU0 : 0 ∈ U := by
    change η 0 ∈ P.openCarrier
    rw [hη0]
    exact P.mem_openCarrier
  have htarget : MapsTo η U P.coordinates.target :=
    fun _ ht => P.carrier_subset_target (P.openCarrier_subset_carrier ht)
  have hcurve : ContDiffOn ℝ ∞ (P.coordinates.symm ∘ η) U :=
    (P.smooth_symm.comp hη.contMDiffOn htarget).contDiffOn
  have hsmooth : ContDiffOn ℝ ∞ (D.edgeVertexGerm P a t₀ d) U :=
    (collarParameterEquiv.contDiff.comp_contDiffOn hcurve).sub contDiffOn_const
  have hzero : D.edgeVertexGerm P a t₀ d 0 = 0 := by
    change collarParameterEquiv (P.coordinates.symm (η 0)) - P.center = 0
    rw [hη0, P.center_eq, collarParameterEquiv.apply_symm_apply, sub_self]
  let g := P.coordinates.symm ∘ (D.edge a.1 a.2).map
  have hpC : (D.edge a.1 a.2).map t₀ ∈ P.coordinates.target :=
    hp ▸ P.carrier_subset_target (P.openCarrier_subset_carrier P.mem_openCarrier)
  have hV : IsOpen ((D.edge a.1 a.2).map ⁻¹' P.coordinates.target) :=
    P.coordinates.open_target.preimage (D.edge_contMDiff a).continuous
  have hg : HasDerivAt g (deriv g t₀) t₀ :=
    ((D.edge_coordinate_contDiffOn a P.coordinates P.smooth_symm).contDiffAt
      (hV.mem_nhds hpC)).differentiableAt (by simp) |>.hasDerivAt
  have hpath : HasDerivAt (fun t : ℝ => t₀ + d * t) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul d).const_add t₀
  have hcomp : HasDerivAt (fun t => g (t₀ + d * t)) (d • deriv g t₀) 0 :=
    hg.scomp_of_eq 0 hpath (by simp)
  have hder : HasDerivAt (D.edgeVertexGerm P a t₀ d)
      (collarParameterEquiv (d • deriv g t₀)) 0 :=
    (collarParameterEquiv.hasFDerivAt.comp_hasDerivAt 0 hcomp).sub_const P.center
  have hregular : deriv (D.edgeVertexGerm P a t₀ d) 0 ≠ 0 := by
    rw [hder.deriv]
    intro hz
    have hdz : d • deriv g t₀ = 0 :=
      collarParameterEquiv.injective (hz.trans (map_zero collarParameterEquiv).symm)
    exact smul_ne_zero hd (D.edge_coordinate_deriv_ne_zero a P.coordinates
      P.smooth P.smooth_symm hpC) hdz
  refine ⟨U, hU, hU0, hsmooth, hzero, hregular, ?_⟩
  intro t ht
  have hcarrier := P.openCarrier_subset_carrier ht
  have haxes := (P.coordinates_mem_circles_iff
    (P.coordinates.map_target (htarget ht))).mp
      (by simpa only [P.coordinates.right_inv (htarget ht)] using
        (hlocal (η t) hcarrier).mp (D.edge_mem_boundary a (t₀ + d * t)))
  have hcoord : (P.coordinates.symm (η t)) 0 = P.center.1 ∨
      (P.coordinates.symm (η t)) 1 = P.center.2 := by
    cases P with
    | single x Q => exact Or.inl haxes
    | crossing x y hxy Q => exact haxes
  change ((P.coordinates.symm (η t)) 0 - P.center.1 = 0) ∨
    ((P.coordinates.symm (η t)) 1 - P.center.2 = 0)
  simpa only [sub_eq_zero] using hcoord

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
