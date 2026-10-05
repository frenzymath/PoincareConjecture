import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Attainment.Minimum.SliceBound
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.MinimizingRegion.Configuration
import PoincareLib.Geometry.Riemannian.Normalization.Connection.Existence
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.CurvatureCalculus
import PoincareLib.Geometry.RicciFlow.Curvature.Construction

/-!
# The minimizing region of an actual confined generalized history

The generic M46 attainment and capped-slice estimates apply on the
literal included strip. Source: MT Proposition 16.4, p. 369 and
pp. 389-391; derivations/seed-m15.md, Stage F.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M47

open Proofs.M46

/-- Actual compact action confinement gives the full minimizing
region on the same generalized geometry and time strip. -/
theorem seedM15_minimizingRegion
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (hM14 : GeneralizedLGeometryTheory.{u} 3)
    {X : Type u} [TopologicalSpace X] {time : X → ℝ} {I : SpacetimeInterval}
    (G : GeneralizedLGeometryTransport 3 X time I)
    {T start : ℝ} (x : (G.slices T).Point)
    (C : ActionConfinement G T start x.val)
    (hstrip : Icc start T ⊆ I.domain) :
    Nonempty (MinimizingRegion G T start x.val C) := by
  let hCoordinates : M12MetricPredecessors.{0} 3 := {
    connection_exists := fun _ _ _ _ _ _ g => normalization_exists_leviCivitaData g
    connection_regular := fun _ _ _ _ _g D _ hU Y hY =>
      D.normalization_contMDiffOn_connection hU Y hY
    curvature_calculus := fun _ _ _ _ _g D => D.normalization_curvatureTensorCalculus }
  obtain ⟨LG⟩ := hM14.conclusion X time I G
  obtain ⟨E⟩ := LG.exponential.family T x.val x.property
  apply minimizingRegion_nonempty_of_slice_comparison ricciFlowCurvatureTheory.{0}
    hM12 LG E C hstrip
  · intro a c ha hc
    exact cappedSliceAction_continuousOn ricciFlowCurvatureTheory.{0}
      hM12 LG E C hstrip ha hc
  · intro b hb hbStart
    exact cappedSliceAction_le_three_mul hCoordinates ricciFlowCurvatureTheory.{0}
      hM12 LG E C hstrip hb hbStart

end PoincareMT.M47
