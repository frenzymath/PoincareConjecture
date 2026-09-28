import PoincareConjecture.Proofs.M12.GeneralizedCylinders
import PoincareConjecture.Proofs.M11.CylinderMetricEvaluation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M12

open PoincareConjecture.Proofs.M11

variable (F : GeneralizedRicciFlowData.{u})
  (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas F))

theorem originalBoxSpatial_derivative (b : F.box_index) (p : (F.box b).carrier.carrier)
    (t : (R.timeIntervals.interval (boxInterval F b)).Point)
    (x : spatialChartDomain (n := 3) p) (v : EuclideanSpace ℝ (Fin 3)) :
    (cylinderSpatialEquiv (originalBoxCylinder F R b) t (spatialChartInverse p x)
      (mfderiv (𝓡 3) (𝓡 3) (spatialChartInverse p) x v)).val =
      ((R.boxMetric ⟨b, p⟩).spatialTangentEquiv t x v).val := by
  rw [cylinderSpatialEquiv_eq, (R.boxMetric ⟨b, p⟩).spatialTangentEquiv_eq]
  have hs := (originalBoxCylinder F R b).smooth.comp
    (contMDiff_const.prodMk contMDiff_id : ContMDiff (𝓡 3) (spacetimeModel 3) ∞
      (fun y : (F.box b).carrier.carrier => (t, y)))
  have h := mfderiv_comp_apply x
    ((hs (spatialChartInverse p x)).mdifferentiableAt (by simp))
    ((spatialChartInverse_smooth p x).mdifferentiableAt (by simp)) v
  have heq : (fun y => (originalBoxCylinder F R b).toSpacetime (t, y)) ∘
      spatialChartInverse p = (fun y => (R.boxCylinder ⟨b, p⟩).toSpacetime (t, y)) :=
    funext fun y => originalBoxMap_chart F R b p (t, y)
  dsimp only [Function.comp_def] at h heq
  rw [heq] at h
  exact h.symm

theorem originalBoxMetric_chart (b : F.box_index) (p : (F.box b).carrier.carrier)
    (t : (R.timeIntervals.interval (boxInterval F b)).Point)
    (x : spatialChartDomain (n := 3) p) (v w : EuclideanSpace ℝ (Fin 3)) :
    cylinderMetricForm (originalBoxCylinder F R b) t (spatialChartInverse p x)
      (mfderiv (𝓡 3) (𝓡 3) (spatialChartInverse p) x v)
      (mfderiv (𝓡 3) (𝓡 3) (spatialChartInverse p) x w) =
      ((F.box b).flow.metric t.val).inner (spatialChartInverse p x)
        (mfderiv (𝓡 3) (𝓡 3) (spatialChartInverse p) x v)
        (mfderiv (𝓡 3) (𝓡 3) (spatialChartInverse p) x w) := by
  let H (q : R.spacetime.Point) (a b : SpacetimeModelVector 3) :=
    R.spacetime.horizontalMetric.inner q (R.spacetime.horizontalProjection q a)
      (R.spacetime.horizontalProjection q b)
  calc
    _ = H ((originalBoxCylinder F R b).toSpacetime (t, spatialChartInverse p x))
        (cylinderSpatialEquiv (originalBoxCylinder F R b) t (spatialChartInverse p x)
          (mfderiv (𝓡 3) (𝓡 3) (spatialChartInverse p) x v)).val
        (cylinderSpatialEquiv (originalBoxCylinder F R b) t (spatialChartInverse p x)
          (mfderiv (𝓡 3) (𝓡 3) (spatialChartInverse p) x w)).val := by
      simp only [H, R.spacetime.horizontalProjection_identity, cylinderMetricForm_apply]
    _ = H ((R.boxCylinder ⟨b, p⟩).toSpacetime (t, x))
        ((R.boxMetric ⟨b, p⟩).spatialTangentEquiv t x v).val
        ((R.boxMetric ⟨b, p⟩).spatialTangentEquiv t x w).val := by
      rw [originalBoxSpatial_derivative, originalBoxSpatial_derivative]
      exact congrArg (fun q => H q
        ((R.boxMetric ⟨b, p⟩).spatialTangentEquiv t x v).val
        ((R.boxMetric ⟨b, p⟩).spatialTangentEquiv t x w).val)
        (originalBoxMap_chart F R b p (t, x))
    _ = ((R.boxMetric ⟨b, p⟩).metric t.val).inner x v w := by
      simp only [H, R.spacetime.horizontalProjection_identity]
      exact ((R.boxMetric ⟨b, p⟩).metric_eq t x v w).symm
    _ = ordinaryChartMetric (F.box b).flow.metric p (t.val, x.val) v w :=
      R.boxMetric_eq ⟨b, p⟩ t x v w
    _ = _ := by
      rw [spatialChartInverse_mfderiv, spatialChartInverse_mfderiv]
      rfl

theorem originalBoxMetric_eq (b : F.box_index)
    (t : (R.timeIntervals.interval (boxInterval F b)).Point)
    (x : (F.box b).carrier.carrier) (v w : EuclideanSpace ℝ (Fin 3)) :
    cylinderMetricForm (originalBoxCylinder F R b) t x v w =
      ((F.box b).flow.metric t.val).inner x v w := by
  let y : spatialChartDomain (n := 3) x :=
    ⟨chartAt (EuclideanSpace ℝ (Fin 3)) x x, mem_chart_target _ x⟩
  have hy : spatialChartInverse x y = x :=
    (chartAt (EuclideanSpace ℝ (Fin 3)) x).left_inv (mem_chart_source _ x)
  let e := (spatialChartInverse_localDiffeomorph x y).mfderivToContinuousLinearEquiv (by simp)
  have hv : mfderiv (𝓡 3) (𝓡 3) (spatialChartInverse x) y (e.symm v) = v :=
    e.apply_symm_apply v
  have hw : mfderiv (𝓡 3) (𝓡 3) (spatialChartInverse x) y (e.symm w) = w :=
    e.apply_symm_apply w
  have h := originalBoxMetric_chart F R b x t y (e.symm v) (e.symm w)
  rw [hv, hw] at h
  exact hy ▸ h

noncomputable def originalBoxMetric (b : F.box_index) :
    SpacetimeCylinderMetric (originalBoxCylinder F R b) where
  metric := (F.box b).flow.metric
  smooth := (F.box b).flow.smooth
  spatialTangentEquiv := cylinderSpatialEquiv (originalBoxCylinder F R b)
  spatialTangentEquiv_eq := cylinderSpatialEquiv_eq (originalBoxCylinder F R b)
  metric_eq := fun t x v w => (originalBoxMetric_eq F R b t x v w).symm

end PoincareConjecture.Proofs.M12
