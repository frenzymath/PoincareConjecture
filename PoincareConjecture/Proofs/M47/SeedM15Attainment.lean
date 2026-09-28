import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.SliceBound
import PoincareConjecture.Proofs.M46.Sec16_1_MinimizingRegion.Configuration
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Normalization.Connection.Existence
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Normalization.Curvature.Calculus
import PoincareConjecture.Proofs.M04

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M46

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

end PoincareConjecture.M47
