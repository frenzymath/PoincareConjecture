import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.StableConfiguration
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.Volume.SmallBallVolume
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Removal.Continuation.RemovalRestriction

/-!
# The larger cylinder in the small-radius case

Morgan--Tian Proposition 16.1, pp. 367-368, using Lemma 11.2 and
Theorem 1.34. A literal controlled cylinder on the terminal doubled ball
gives a larger admissible test and transfers its noncollapse to smaller
balls. The cylinder's production remains a separate geometric statement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareMT.Proofs.M46

/-- The actual low-scalar cylinder needed below the auxiliary test radius.
Its time, center and physical maps belong to the original observed flow. -/
structure LowScalarCylinder {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (D : NoncollapseTest F O) (rho : ℝ) where
  cylinder : SurgeryFlowCylinder F (F.slice D.time) D.time 1
    (Icc (-rho ^ 2) 0) ((F.metric D.time).ball D.center (2 * rho))
  based : ∀ h y, y ∈ (F.metric D.time).ball D.center (2 * rho) →
    HEq (cylinder.forward 0 h y) y
  curvature : ∀ s hs y, y ∈ (F.metric D.time).ball D.center (2 * rho) →
    (F.connection (D.time + s / 1)).curvatureTensorNorm
      (cylinder.forward s hs y) ≤ rho⁻¹ ^ 2

/-- Spatial restriction gives an actual radius-rho test with unchanged
time, center and positive-component exemption. -/
def LowScalarCylinder.test {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    {D : NoncollapseTest F O} {rho : ℝ} (C : LowScalarCylinder D rho)
    (hrho : 0 < rho) (hrho_le : rho ≤ F.parameters.epsilon) : NoncollapseTest F O := by
  have hball : (F.metric D.time).ball D.center rho ⊆
      (F.metric D.time).ball D.center (2 * rho) := by
    intro y hy
    exact hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  exact {
    time := D.time
    time_mem := D.time_mem
    time_domain := D.time_domain
    center := D.center
    not_positive := D.not_positive
    radius := rho
    radius_pos := hrho
    radius_le := hrho_le
    cylinder := M44.restrictCylinderSource C.cylinder hball
    based := fun h y hy => C.based h y (hball hy)
    curvature := fun s hs y hy => C.curvature s hs y (hball hy)
  }

/-- The literal zero-time identity bounds full curvature on the physical
doubled ball, which is the domain needed for local volume comparison. -/
theorem LowScalarCylinder.terminal_curvature
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    {D : NoncollapseTest F O} {rho : ℝ} (C : LowScalarCylinder D rho)
    {y : (F.slice D.time).carrier}
    (hy : y ∈ (F.metric D.time).ball D.center (2 * rho)) :
    (F.connection D.time).curvatureTensorNorm y ≤ rho⁻¹ ^ 2 := by
  have hzero : (0 : ℝ) ∈ Icc (-rho ^ 2) 0 := ⟨by nlinarith [sq_nonneg rho], le_rfl⟩
  have h := C.curvature 0 hzero y hy
  have hp : (⟨D.time + 0 / 1, C.cylinder.forward 0 hzero y⟩ :
      (t : ℝ) × (F.slice t).carrier) = ⟨D.time, y⟩ :=
    Sigma.ext (by simp) (C.based hzero y hy)
  have hnorm := congrArg (fun p : (t : ℝ) × (F.slice t).carrier =>
    (F.connection p.1).curvatureTensorNorm p.2) hp
  exact hnorm ▸ h

/-- The larger test's actual stable source yields the required volume at
every smaller tested radius, with a loss fixed before the surgery scale. -/
theorem LowScalarCylinder.small_volume (P : M46Predecessors.{u})
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {taubar l0 V : ℝ} (U : M15GeneralizedUniformData.{u} 3 taubar l0 V)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    {D : NoncollapseTest F O} {rho : ℝ} (C : LowScalarCylinder D rho)
    (hrho : 0 < rho) (hrho_le : rho ≤ F.parameters.epsilon)
    (hsmall : D.radius ≤ rho)
    {H : HalfRadiusHistory (C.test hrho hrho_le)}
    (source : StableSource H taubar l0 V) :
    ENNReal.ofReal (smallBallLoss * configurationKappa p U * D.radius ^ 3) ≤
      calibratedMetricVolume (F.metric D.time) ((F.metric D.time).ball D.center D.radius) := by
  have hvolume := source.volume P p U
  have hcompact : IsCompact (closure ((F.metric D.time).ball D.center (2 * rho))) :=
    (F.slices_compact D.time D.time_domain).of_isClosed_subset isClosed_closure
      (subset_univ _)
  exact calibrated_small_ball_lower_bound (F.metric D.time) (F.connection D.time)
    D.center hrho D.radius_pos hsmall (configurationKappa_pos p U)
    hcompact (fun _ hy => C.terminal_curvature hy) hvolume

end PoincareMT.Proofs.M46
