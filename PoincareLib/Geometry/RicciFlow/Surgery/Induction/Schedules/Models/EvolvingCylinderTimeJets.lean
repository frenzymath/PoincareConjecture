import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Collar.Cylinder.EvolvingCylinderField
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scalar.Calculus.ScalarFourJet

/-!
# Continuous time dependence of all spatial cylinder jets

The evolving cylinder metric is affine in time, and spatial differentiation
preserves that dependence. This includes the redundant native four-jet
used by the scalar Laplacian. Source: Morgan--Tian Proposition 15.2,
pp. 353-354, and equation (3.7), p. 41.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Native four-jets retain nested coefficient and derivative instances.
set_option maxSynthPendingDepth 16

open scoped ContDiff Topology

open PoincareMT.MetricSurgery

namespace PoincareMT.M45

open M36 M44 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Z" =>
  (cylinderHeightCovector.smulRight cylinderHeightCovector : MetricCoefficient 3)
local notation "Z₂" => ((Z, 0, 0) : MetricTwoJet 3)

noncomputable local instance timeJetCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance timeJetCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance timeJetTwoJetNormedGroup :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance timeJetTwoJetNormedSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

noncomputable local instance timeJetTwoJetTopologicalAddGroup :
    IsTopologicalAddGroup (MetricTwoJet 3) := SeminormedAddCommGroup.toIsTopologicalAddGroup

noncomputable local instance timeJetFirstNormedGroup :
    NormedAddCommGroup (E →L[ℝ] MetricTwoJet 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance timeJetFirstNormedSpace :
    NormedSpace ℝ (E →L[ℝ] MetricTwoJet 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance timeJetFirstTopologicalAddGroup :
    IsTopologicalAddGroup (E →L[ℝ] MetricTwoJet 3) :=
      SeminormedAddCommGroup.toIsTopologicalAddGroup

noncomputable local instance timeJetSecondNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] MetricTwoJet 3) :=
      ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance timeJetSecondNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] MetricTwoJet 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance timeJetArrayNormedGroup :
    NormedAddCommGroup (Fin 3 → MetricTwoJet 3) := Pi.normedAddCommGroup

noncomputable local instance timeJetArrayNormedSpace :
    NormedSpace ℝ (Fin 3 → MetricTwoJet 3) := Pi.normedSpace

noncomputable local instance timeJetFourJetNormedGroup :
    NormedAddCommGroup (ScalarMetricFourJet 3) := Prod.normedAddCommGroup

noncomputable local instance timeJetFourJetNormedSpace :
    NormedSpace ℝ (ScalarMetricFourJet 3) := Prod.normedSpace

/-- Every fixed spatial derivative varies affinely with model time.
Source: the round-cylinder family in Proposition 15.2, pp. 353-354. -/
theorem model_evolvingCylinder_iteratedFDeriv (m : ℕ) (t : ℝ) (x : E) :
    iteratedFDeriv ℝ m (evolvingCylinderModelField t) x =
      (1 - t) • iteratedFDeriv ℝ m cylinderModelField x +
        t • iteratedFDeriv ℝ m (fun _ : E => Z) x := by
  have hs : ContDiffAt ℝ (m : ℕ∞ω) cylinderModelField x :=
    cylinderModelField_contDiff.contDiffAt.of_le (by exact_mod_cast le_top)
  have hz : ContDiffAt ℝ (m : ℕ∞ω) (fun _ : E => Z) x := contDiffAt_const
  change iteratedFDeriv ℝ m ((1 - t) • cylinderModelField + t • (fun _ : E => Z)) x = _
  calc
    _ = iteratedFDeriv ℝ m ((1 - t) • cylinderModelField) x +
        iteratedFDeriv ℝ m (t • (fun _ : E => Z)) x :=
      iteratedFDeriv_add_apply (hs.const_smul (1 - t)) (hz.const_smul t)
    _ = _ := by rw [iteratedFDeriv_const_smul_apply hs, iteratedFDeriv_const_smul_apply hz]

/-- Time continuity holds for every finite spatial derivative order,
at every spatial point. Source: Proposition 15.2, pp. 353-354. -/
theorem continuous_model_evolvingCylinder_iteratedFDeriv (m : ℕ) (x : E) :
    Continuous (fun t : ℝ => iteratedFDeriv ℝ m (evolvingCylinderModelField t) x) := by
  simp_rw [model_evolvingCylinder_iteratedFDeriv]
  fun_prop

/-- The affine two-jet identity holds throughout the spatial chart.
Source: the evolving cylinder in Proposition 15.2, pp. 353-354. -/
theorem model_evolvingCylinder_twoJet (t : ℝ) (x : E) :
    metricTwoJet (evolvingCylinderModelField t) x =
      (1 - t) • metricTwoJet cylinderModelField x + t • Z₂ := by
  simp only [metricTwoJet, evolvingCylinderModelField_fderiv,
    evolvingCylinderModelField_second_fderiv, evolvingCylinderModelField,
    Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero]

set_option synthInstance.maxHeartbeats 100000 in
-- Differentiating the nested two-jet requires matching its native product topology.
/-- Spatial derivatives of the two-jet have the same horizontal
time factor. Source: Proposition 15.2, pp. 353-354. -/
theorem model_evolvingCylinder_twoJet_fderiv (t : ℝ) (x : E) :
    fderiv ℝ (metricTwoJet (evolvingCylinderModelField t)) x =
      (1 - t) • fderiv ℝ (metricTwoJet cylinderModelField) x := by
  have heq : metricTwoJet (evolvingCylinderModelField t) =
      fun y => (1 - t) • metricTwoJet cylinderModelField y + t • Z₂ :=
    funext (model_evolvingCylinder_twoJet t)
  have hJ : ContDiffAt ℝ ∞ (metricTwoJet cylinderModelField) x :=
    contDiffAt_metricTwoJet cylinderModelField_contDiff.contDiffAt
  have hD : HasFDerivAt (metricTwoJet cylinderModelField)
      (fderiv ℝ (metricTwoJet cylinderModelField) x) x :=
    (hJ.differentiableAt (by simp)).hasFDerivAt
  have hA : HasFDerivAt
      (fun y => (1 - t) • metricTwoJet cylinderModelField y + t • Z₂)
      ((1 - t) • fderiv ℝ (metricTwoJet cylinderModelField) x) x :=
    (hD.const_smul (1 - t)).add_const (t • Z₂)
  rw [heq]
  exact hA.fderiv

set_option synthInstance.maxHeartbeats 100000 in
-- The derivative target uses the native continuous-linear topology on two-jets.
set_option maxHeartbeats 800000 in
-- The second derivative identifies nested native continuous-linear instances.
/-- The second derivative of the two-jet is affine in model time.
Source: Proposition 15.2, pp. 353-354, and equation (3.7), p. 41. -/
theorem model_evolvingCylinder_twoJet_second_fderiv (t : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (metricTwoJet (evolvingCylinderModelField t))) x =
      (1 - t) • fderiv ℝ (fderiv ℝ (metricTwoJet cylinderModelField)) x := by
  have heq : fderiv ℝ (metricTwoJet (evolvingCylinderModelField t)) =
      fun y => (1 - t) • fderiv ℝ (metricTwoJet cylinderModelField) y :=
    funext (model_evolvingCylinder_twoJet_fderiv t)
  have hJ : ContDiffAt ℝ ∞ (metricTwoJet cylinderModelField) x :=
    contDiffAt_metricTwoJet cylinderModelField_contDiff.contDiffAt
  have hD : HasFDerivAt (fderiv ℝ (metricTwoJet cylinderModelField))
      (fderiv ℝ (fderiv ℝ (metricTwoJet cylinderModelField)) x) x :=
    ((hJ.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  rw [heq]
  exact (hD.const_smul (1 - t)).fderiv

/-- The native scalar four-jet is affine in model time. Its extra
axial term has no spatial derivatives. Source: Proposition 15.2, pp. 353-354. -/
theorem model_evolvingCylinder_fourJet (t : ℝ) (x : E) :
    scalarMetricFourJet (evolvingCylinderModelField t) x =
      ((1 - t) • metricTwoJet cylinderModelField x + t • Z₂,
        (fun i => (1 - t) • (scalarMetricFourJet cylinderModelField x).2.1 i),
        (fun i j => (1 - t) • (scalarMetricFourJet cylinderModelField x).2.2 i j)) := by
  simp only [scalarMetricFourJet, model_evolvingCylinder_twoJet,
    model_evolvingCylinder_twoJet_fderiv, model_evolvingCylinder_twoJet_second_fderiv,
    smul_apply]

/-- Closed model-time intervals have compact native four-jet images.
Source: the uniform cylinder approximation in Proposition 15.2, pp. 353-354. -/
theorem continuous_model_evolvingCylinder_fourJet (x : E) :
    Continuous (fun t : ℝ => scalarMetricFourJet (evolvingCylinderModelField t) x) := by
  simp_rw [model_evolvingCylinder_fourJet]
  fun_prop

end PoincareMT.M45
