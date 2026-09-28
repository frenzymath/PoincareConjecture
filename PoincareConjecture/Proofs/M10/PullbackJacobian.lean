import PoincareConjecture.Proofs.M10.PullbackMetric
import PoincareConjecture.Proofs.M10.Calibration
import Mathlib.Analysis.InnerProductSpace.NormDet

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def pullbackJacobian (g : RiemannianMetric n M)
    (f : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (Matrix.det (fun i j : Fin n ↦ pullbackMetricForm g f x
    (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)))

set_option backward.isDefEq.respectTransparency false in

theorem pullbackJacobian_eq_normDet (g : RiemannianMetric n M)
    (f : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    pullbackJacobian g f x = LinearMap.normDet
      (U := EuclideanSpace ℝ (Fin n)) (V := TangentSpace (𝓡 n) (f x))
      (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let D : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] TangentSpace (𝓡 n) (f x) :=
    (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap
  have hsq := D.normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin n) ℝ)
  rw [RCLike.ofReal_real_eq_id, id_eq] at hsq
  change Real.sqrt (Matrix.gram ℝ (fun i ↦ D (EuclideanSpace.basisFun (Fin n) ℝ i))).det =
    D.normDet
  rw [← hsq, Real.sqrt_sq D.normDet_nonneg]

theorem pullbackJacobian_nonneg (g : RiemannianMetric n M)
    (f : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ pullbackJacobian g f x := Real.sqrt_nonneg _

set_option backward.isDefEq.respectTransparency false in

theorem pullbackJacobian_pos (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hD : Function.Injective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    0 < pullbackJacobian g f x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [pullbackJacobian_eq_normDet]
  let D : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] TangentSpace (𝓡 n) (f x) :=
    (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap
  change 0 < D.normDet
  refine lt_of_le_of_ne D.normDet_nonneg ?_
  exact Ne.symm (fun h ↦ LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp h
    (LinearMap.ker_eq_bot.mpr hD))

theorem pullbackJacobian_continuousAt (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) 1 f x) :
    ContinuousAt (pullbackJacobian g f) x := by
  have hB := pullbackMetricForm_continuousAt g hf
  have hmatrix : ContinuousAt (fun y ↦ (fun i j : Fin n ↦ pullbackMetricForm g f y
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j))) x :=
    continuousAt_pi.mpr fun _ ↦ continuousAt_pi.mpr fun _ ↦
      (hB.clm_apply continuousAt_const).clm_apply continuousAt_const
  exact Real.continuous_sqrt.continuousAt.comp
    (continuous_id.matrix_det.continuousAt.comp hmatrix)

theorem eventually_pullbackJacobian_comparison (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) 1 f x)
    (hD : Function.Injective (mfderiv (𝓡 n) (𝓡 n) f x))
    {r : ℝ} (hr : 1 < r) :
    ∀ᶠ y in 𝓝 x, pullbackJacobian g f x / r ≤ pullbackJacobian g f y ∧
      pullbackJacobian g f y ≤ r * pullbackJacobian g f x := by
  have hJ := pullbackJacobian_pos g hD
  have hlo : pullbackJacobian g f x / r < pullbackJacobian g f x :=
    (div_lt_self hJ hr).trans_le le_rfl
  have hhi : pullbackJacobian g f x < r * pullbackJacobian g f x := by nlinarith
  have hcont := pullbackJacobian_continuousAt g hf
  filter_upwards [hcont (eventually_gt_nhds hlo), hcont (eventually_lt_nhds hhi)]
    with y hylo hyhi
  exact ⟨hylo.le, hyhi.le⟩

theorem volume_linear_image_eq_normDet_mul
    (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (A : Set (EuclideanSpace ℝ (Fin n))) :
    volume (L '' A) = ENNReal.ofReal L.normDet * volume A := by
  have hH := L.hausdorffMeasure_image A
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hH
  rw [← euclideanVolumeCalibration_smul_hausdorff n,
    Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul, hH]
  exact mul_left_comm _ _ _

end PoincareConjecture.M10
