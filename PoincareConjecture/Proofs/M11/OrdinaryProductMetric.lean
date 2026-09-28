import PoincareConjecture.Proofs.M11.OrdinaryCylinder
import PoincareConjecture.Proofs.M11.BoxCylinderMetric
import PoincareConjecture.Proofs.M11.CylinderMetricEvaluation





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] [SecondCountableTopology M] [Nonempty M]

theorem ordinaryProduct_spatialEquiv_box (g : ℝ → RiemannianMetric n M)
    (I : SpacetimeInterval) (hg : RiemannianMetric.IsSmoothFamilyOn g I.domain)
    (b : M) (t : (smoothInterval I).Point) (x : spatialChartDomain (n := n) b)
    (v : EuclideanSpace ℝ (Fin n)) :
    cylinderSpatialEquiv (ordinaryProductCylinder g I hg) t (spatialChartInverse b x)
        (mfderiv (𝓡 n) (𝓡 n) (spatialChartInverse b) x v) =
      cylinderSpatialEquiv (adaptedBoxCylinder (ordinaryAtlas g I hg) b) t x v := by
  apply Subtype.ext
  rw [cylinderSpatialEquiv_eq, cylinderSpatialEquiv_eq]
  have hs := (ordinaryProductCylinder g I hg).smooth.comp
    (contMDiff_const.prodMk contMDiff_id : ContMDiff (𝓡 n) (spacetimeModel n) ∞
      (fun y : M ↦ (t, y)))
  exact (mfderiv_comp_apply x ((hs (spatialChartInverse b x)).mdifferentiableAt (by simp))
    ((spatialChartInverse_smooth b x).mdifferentiableAt (by simp)) v).symm

theorem ordinaryProduct_metric_box (g : ℝ → RiemannianMetric n M)
    (I : SpacetimeInterval) (hg : RiemannianMetric.IsSmoothFamilyOn g I.domain)
    (b : M) (t : (smoothInterval I).Point) (x : spatialChartDomain (n := n) b)
    (v w : EuclideanSpace ℝ (Fin n)) :
    cylinderMetricForm (ordinaryProductCylinder g I hg) t (spatialChartInverse b x)
        (mfderiv (𝓡 n) (𝓡 n) (spatialChartInverse b) x v)
        (mfderiv (𝓡 n) (𝓡 n) (spatialChartInverse b) x w) =
      (g t.val).inner (spatialChartInverse b x)
        (mfderiv (𝓡 n) (𝓡 n) (spatialChartInverse b) x v)
        (mfderiv (𝓡 n) (𝓡 n) (spatialChartInverse b) x w) := by
  have hc := adaptedBox_metric_eq (ordinaryAtlas g I hg) b t x v w
  change cylinderMetricForm (adaptedBoxCylinder (ordinaryAtlas g I hg) b)
    (cylinderMetricTime I t.val) x v w = _ at hc
  rw [cylinderMetricTime_of_mem] at hc
  calc
    _ = cylinderMetricForm (adaptedBoxCylinder (ordinaryAtlas g I hg) b) t x v w := by
      rw [cylinderMetricForm_apply, cylinderMetricForm_apply,
        ordinaryProduct_spatialEquiv_box, ordinaryProduct_spatialEquiv_box]
      rfl
    _ = ordinaryChartMetric g b (t.val, x.val) v w := hc
    _ = _ := by
      rw [spatialChartInverse_mfderiv, spatialChartInverse_mfderiv]
      rfl

theorem ordinaryProduct_metric_eq (g : ℝ → RiemannianMetric n M)
    (I : SpacetimeInterval) (hg : RiemannianMetric.IsSmoothFamilyOn g I.domain)
    (t : (smoothInterval I).Point) (x : M) (v w : EuclideanSpace ℝ (Fin n)) :
    cylinderMetricForm (ordinaryProductCylinder g I hg) t x v w =
      (g t.val).inner x v w := by
  let y : spatialChartDomain (n := n) x :=
    ⟨chartAt (EuclideanSpace ℝ (Fin n)) x x, mem_chart_target _ x⟩
  have hy : spatialChartInverse x y = x :=
    (chartAt (EuclideanSpace ℝ (Fin n)) x).left_inv (mem_chart_source _ x)
  let e := (spatialChartInverse_localDiffeomorph x y).mfderivToContinuousLinearEquiv (by simp)
  have hv : mfderiv (𝓡 n) (𝓡 n) (spatialChartInverse x) y (e.symm v) = v :=
    e.apply_symm_apply v
  have hw : mfderiv (𝓡 n) (𝓡 n) (spatialChartInverse x) y (e.symm w) = w :=
    e.apply_symm_apply w
  have h := ordinaryProduct_metric_box g I hg x t y (e.symm v) (e.symm w)
  rw [hv, hw] at h
  exact hy ▸ h

noncomputable def ordinaryProductMetric (g : ℝ → RiemannianMetric n M)
    (I : SpacetimeInterval) (hg : RiemannianMetric.IsSmoothFamilyOn g I.domain) :
    SpacetimeCylinderMetric (ordinaryProductCylinder g I hg) where
  metric := g
  smooth := hg
  spatialTangentEquiv := cylinderSpatialEquiv (ordinaryProductCylinder g I hg)
  spatialTangentEquiv_eq := cylinderSpatialEquiv_eq (ordinaryProductCylinder g I hg)
  metric_eq := fun t x v w ↦ (ordinaryProduct_metric_eq g I hg t x v w).symm

end PoincareConjecture.Proofs.M11
