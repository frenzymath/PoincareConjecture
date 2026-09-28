import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.AmbientSectorCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph Plane M} {a b : ℝ}
  {G : D.OrientedGraphPiece e R C a b} {ua wa ub wb : ℝ}
  {P : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb}
  {δ ra rb : ℝ} (B : G.FixedStripBandFaces P δ ra rb)

noncomputable def ambientTopPoint (t : ℝ) : Plane :=
  G.frame.symm (B.faces.cuts.coordinates B.faces.open_domain B.faces.smooth_lower
    (t, B.faces.height t))

theorem ambientTopPoint_map (t : ℝ) :
    C (B.ambientTopPoint t) = G.strip P (t, B.faces.height t) := by
  rw [← B.coordinates_eq]
  change C (B.ambientTopPoint t) =
    linearGraphCoordinates C G.frame (collarParameterEquiv.symm
      (B.faces.cuts.coordinates B.faces.open_domain B.faces.smooth_lower
        (collarParameterEquiv (collarParameterEquiv.symm (t, B.faces.height t)))))
  rw [linearGraphCoordinates_apply, collarParameterEquiv.apply_symm_apply,
    collarParameterEquiv.apply_symm_apply]
  rfl

theorem ambientTopPoint_mem_source {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    B.ambientTopPoint t ∈ C.source := by
  have hband : collarParameterEquiv.symm (t, B.faces.height t) ∈ B.faces.band := by
    rw [B.faces.band_eq_subgraph]
    simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply] using
      And.intro ht (And.intro (B.faces.height_pos ht).le le_rfl)
  have hs := (B.faces.band_subset_source hband).2.2
  change G.frame.symm (collarParameterEquiv (collarParameterEquiv.symm
    (B.faces.cuts.coordinates B.faces.open_domain B.faces.smooth_lower
      (collarParameterEquiv (collarParameterEquiv.symm (t, B.faces.height t)))))) ∈ C.source at hs
  simpa only [ambientTopPoint, collarParameterEquiv.apply_symm_apply] using hs

theorem ambientTopFunctional_topPoint (i : Fin B.faces.interface.count) {t : ℝ}
    (ht : t ∈ Icc (B.faces.cut i.castSucc) (B.faces.cut i.succ)) :
    B.ambientTopFunctional i (B.ambientTopPoint t) = 0 := by
  have he := (B.faces.interface.pieceCoordinates B.faces.open_domain B.faces.smooth_lower i).strip_upperGraph_eq ht
  change B.faces.topLineExcess i (collarParameterEquiv.symm
    (G.frame (G.frame.symm (B.faces.cuts.coordinates B.faces.open_domain
      B.faces.smooth_lower (t, B.faces.height t))))) = 0
  rw [G.frame.apply_symm_apply]
  change (B.faces.cuts.coordinates B.faces.open_domain B.faces.smooth_lower
      (t, B.faces.height t)).2 - B.faces.interface.piece i
        (B.faces.cuts.coordinates B.faces.open_domain B.faces.smooth_lower
          (t, B.faces.height t)).1 = 0
  rw [B.faces.height_eq_upperGraph ht, B.faces.cuts.coordinates_apply, he]
  exact sub_self _

theorem ambient_carrier_open_top_halfspace
    (i : Fin B.faces.interface.count) {t : ℝ}
    (ht : t ∈ Ioo (B.faces.cut i.castSucc) (B.faces.cut i.succ)) :
    C.symm '' B.faces.carrier =ᶠ[𝓝 (B.ambientTopPoint t)]
      {z | B.ambientTopFunctional i z ≤ 0} := by
  have hc : ContinuousAt (fun z : Plane => collarParameterEquiv.symm (G.frame z))
      (B.ambientTopPoint t) :=
    (collarParameterEquiv.symm.continuous.comp G.frame.continuous).continuousAt
  have hv : collarParameterEquiv.symm (G.frame (B.ambientTopPoint t)) =
      collarParameterEquiv.symm (B.faces.cuts.coordinates B.faces.open_domain
        B.faces.smooth_lower (t, B.faces.upperGraph i t)) := by
    simp only [ambientTopPoint, G.frame.apply_symm_apply,
      B.faces.height_eq_upperGraph ⟨ht.1.le, ht.2.le⟩]
  have hlocal := hc.eventually (by
    simpa only [hv] using B.faces.planar_carrier_open_top_eventually_iff i ht)
  filter_upwards [hlocal] with z hz
  apply propext
  change z ∈ C.symm '' B.faces.carrier ↔ B.ambientTopFunctional i z ≤ 0
  rw [mem_chart_image_iff_mem_linearGraphCoordinates_image C G.frame B.faces.carrier]
  exact hz

end FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces
end PoincareConjecture.Topology.Surface
