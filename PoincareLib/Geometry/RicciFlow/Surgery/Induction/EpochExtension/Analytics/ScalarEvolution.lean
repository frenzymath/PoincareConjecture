import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Analytics.LaplacianTransport
import PoincareLib.Geometry.RicciFlow.Surgery.Control.Basic

/-!
# Scalar time control on the actual ordinary slabs

The scalar evolution formula (Morgan-Tian Theorem 3.13, Eq. (3.7), p. 41)
turns a given guarded spatial analytic estimate into time-derivative control.
All spatial operators are transported through the actual slab map. This
does not produce the analytic estimate or assert control at a surgery jump.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

/-- A supplied guarded analytic estimate implies the scalar time estimate
on every actual ordinary slab at interior times, with the same threshold
and constant. Only existing M04/M13 theorem services are used. -/
theorem SurgeryHighCurvatureAnalyticOn.scalar_derivative
    {F : SurgeryFlowData.{u}} {J : Set ℝ} {r C : ℝ}
    (h : SurgeryHighCurvatureAnalyticOn F J r C) :
    SurgeryScalarDerivativeControlOn F J r C := by
  intro a b hab hJ hS x t ht hR
  let B := F.regular_slabs a b hab hJ hS
  let tB : Set.Icc a b := ⟨t, ht.2.1.le, ht.2.2.le⟩
  have hscalar := B.m48_scalarCurvature_eq tB (F.connection t) x
  have hguard : r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature (B.identify tB x) := by
    rw [hscalar]
    exact hR
  have hbound := (h t ht.1 (hJ tB.2) (B.identify tB x) hguard).2
  rw [B.m48_scalarLaplacian_eq tB (F.connection t) x,
    B.m48_ricciNormSq_eq tB (F.connection t) x, hscalar] at hbound
  refine ⟨(B.flow.connection t).laplacian (B.flow.connection t).scalarCurvature x +
    2 * (B.flow.connection t).ricciNormSq x, ?_, hbound⟩
  exact (B.flow.hasDerivWithinAt_scalarCurvature t tB.2 x).hasDerivAt
    (Icc_mem_nhds ht.2.1 ht.2.2)

end PoincareMT
