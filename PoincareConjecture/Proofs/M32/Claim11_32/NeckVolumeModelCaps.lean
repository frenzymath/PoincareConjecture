import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.ModelVolume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Stereographic.Transition
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Euclidean
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Measure
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SpatialEmbedding

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M32

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

def neckModelCap (q : UnitTwoSphere) (a : ℝ) : Set UnitTwoSphere :=
  (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm '' Metric.ball 0 a

def neckModelDiskArea : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal

theorem neckModelDiskArea_pos : 0 < neckModelDiskArea := by
  exact ENNReal.toReal_pos
    (Metric.measure_ball_pos volume _ (by norm_num : (0 : ℝ) < 1)).ne'
    measure_ball_lt_top.ne

theorem neckModelCap_open (q : UnitTwoSphere) (a : ℝ) : IsOpen (neckModelCap q a) := by
  apply (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm.isOpen_image_of_subset_source
    Metric.isOpen_ball
  simpa only [OpenPartialHomeomorph.symm_source, sphere_chart_target] using
    (subset_univ (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a))

theorem neckModelCap_area_lower (q : UnitTwoSphere) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ENNReal.ofReal (neckModelDiskArea * a ^ 2 / 2) ≤
      roundCylinderCrossSectionVolumeMeasure (neckModelCap q a) := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let e := c.symm.restrOpen (Metric.ball 0 1) Metric.isOpen_ball
  let g := RiemannianMetric.euclideanMetric 2
  let h := roundSphereMetric 2
  have he : ContMDiffOn (𝓡 2) (𝓡 2) 1 e e.source :=
    ((sphere_chart_symm_contMDiff q).of_le (by simp)).contMDiffOn
  have hei : ContMDiffOn (𝓡 2) (𝓡 2) 1 e.symm e.target :=
    ((contMDiffOn_chart (I := 𝓡 2) (x := q) (n := (∞ : ℕ∞ω))).of_le (by simp)).mono
      (fun _ hx => hx.1)
  have hD : e.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨he.mdifferentiableOn one_ne_zero, hei.mdifferentiableOn one_ne_zero⟩
  have hnorm : ∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 2) x,
      g.tangentNorm x v ≤ 2 * h.tangentNorm (e x) (mfderiv (𝓡 2) (𝓡 2) e x v) := by
    intro x hx v
    have hxnorm : ‖x‖ ≤ 1 := by
      simpa only [dist_zero_right] using (show dist x 0 < 1 from hx.2).le
    have hl := (roundSphere_chart_quadratic_bounds q hxnorm v).1
    change (16 / (1 ^ 2 + 4) ^ 2) * ‖v‖ ^ 2 ≤
      h.inner (e x) (mfderiv (𝓡 2) (𝓡 2) e x v)
        (mfderiv (𝓡 2) (𝓡 2) e x v) at hl
    have hsq : ‖v‖ ^ 2 ≤ 4 * h.inner (e x)
        (mfderiv (𝓡 2) (𝓡 2) e x v) (mfderiv (𝓡 2) (𝓡 2) e x v) := by
      norm_num at hl
      nlinarith [sq_nonneg ‖v‖]
    have hs := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hs
    have hs4 : Real.sqrt (4 : ℝ) = 2 := by
      convert Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num) using 1
      norm_num
    rw [hs4] at hs
    exact (RiemannianMetric.euclideanMetric_tangentNorm x
      (v : EuclideanSpace ℝ (Fin 2))).trans_le hs
  have hinverse := g.inverse_tangentNorm_le_of_le h e hD (V := e.source) Subset.rfl hnorm
  have hinverse' : ∀ z ∈ e.target, ∀ v : TangentSpace (𝓡 2) z,
      g.tangentNorm (e.symm z) (mfderiv (𝓡 2) (𝓡 2) e.symm z v) ≤
        2 * h.tangentNorm z v := by
    simpa only [e.image_source_eq_target] using hinverse
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a ⊆ e.source := by
    intro x hx
    exact ⟨by simp [c, sphere_chart_target], Metric.ball_subset_ball ha1 hx⟩
  have hvol := g.volumeMeasure_le_image_of_inverse_tangentNorm_le h e hei
    (by norm_num : (0 : ℝ) < 2) hinverse' Metric.isOpen_ball.measurableSet hsub
  have hscale : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a) =
      ENNReal.ofReal (neckModelDiskArea * a ^ 2) := by
    have hmul := Measure.addHaar_ball_mul_of_pos
      (volume : Measure (EuclideanSpace ℝ (Fin 2))) 0 ha (1 : ℝ)
    norm_num only [mul_one, finrank_euclideanSpace, Fintype.card_fin] at hmul
    rw [hmul, ENNReal.ofReal_mul neckModelDiskArea_pos.le,
      ENNReal.ofReal_pow ha.le, neckModelDiskArea,
      ENNReal.ofReal_toReal measure_ball_lt_top.ne]
    exact mul_comm _ _
  have hv : ENNReal.ofReal (neckModelDiskArea * a ^ 2) ≤
      4 * h.volumeMeasure (neckModelCap q a) := by
    simpa only [g, RiemannianMetric.euclideanMetric_volumeMeasure, hscale,
      ENNReal.ofReal_ofNat, show (2 : ℝ≥0∞) ^ 2 = 4 by norm_num, e,
      OpenPartialHomeomorph.coe_restrOpen, c, neckModelCap] using hvol
  have hmodel : roundCylinderCrossSectionVolumeMeasure (neckModelCap q a) =
      2 * h.volumeMeasure (neckModelCap q a) := by
    unfold roundCylinderCrossSectionVolumeMeasure
    rw [rescaledMetric_volumeMeasure, Measure.smul_apply, smul_eq_mul,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg 2), Real.sq_sqrt (by norm_num)]
    norm_num only [ENNReal.ofReal_ofNat]
    rfl
  rw [hmodel, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num only [ENNReal.ofReal_ofNat]
  apply (ENNReal.div_le_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)).mpr
  convert hv using 1
  ring

end PoincareConjecture.M32
