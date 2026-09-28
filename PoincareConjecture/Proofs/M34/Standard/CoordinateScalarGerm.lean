import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Convergence.Curvature

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.FlowCarrier

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem scalarCurvature_eq_of_frozen_coordinate_germ
    {n : ℕ} (C : FlowCarrier n) (gM : C.metric)
    (DM : @LeviCivitaData n C.carrier C.topologicalSpace C.chartedSpace C.isManifold gM)
    (q : C.carrier) (t : ℝ) (p : EuclideanSpace ℝ (Fin n))
    (hp :
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      p ∈ (extChartAt (𝓡 n) q).target)
    (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (DE : LeviCivitaData gE)
    (h : ∀ᶠ x in 𝓝 p, ∀ a b : Fin n,
      gE.euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b) =
      C.coordinateCoefficient q (fun _ y v w => C.metricInner gM y v w) a b (t, x)) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    DE.scalarCurvature p = DM.scalarCurvature ((extChartAt (𝓡 n) q).symm p) := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let c := extChartAt (𝓡 n) q
  obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp
    (inter_mem (extChartAt_target_mem_nhds' hp) h)
  apply DE.scalarCurvature_eq_of_local_isometry DM hVo
    (fun x hx => (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q
      (hV hx).1).contMDiffAt (extChartAt_target_mem_nhds' (hV hx).1)
        |>.contMDiffWithinAt) (x := p) (hx := hpV)
  intro x hx
  have hB : gE.euclideanCoefficients x = gM.pullbackCoefficients c.symm x := by
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
    intro a
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
    exact (hV hx).2 a
  intro u v
  exact congrArg (fun B => B u v) hB

end PoincareConjecture.FlowCarrier
