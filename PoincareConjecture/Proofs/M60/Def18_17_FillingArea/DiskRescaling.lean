import PoincareConjecture.Proofs.M60.Mathlib.ManifoldDerivativeScaling
import PoincareConjecture.Proofs.M60.Mathlib.SetIntegralScaling
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaEnergy
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Pointwise

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60AreaGram_comp_smul (g : RiemannianMetric n M)
    (f : LoopPlane → M) (c : ℝ) (z : LoopPlane) :
    m60AreaGram g (fun x => f (c • x)) z = c ^ 2 • m60AreaGram g f (c • z) := by
  ext i j
  simp only [m60AreaGram, M60.mfderiv_comp_smul, smul_apply,
    Matrix.smul_apply, smul_eq_mul, map_smul]
  ring_nf
  rfl

theorem m60AreaDensity_comp_smul (g : RiemannianMetric n M)
    (f : LoopPlane → M) (c : ℝ) (z : LoopPlane) :
    m60AreaDensity g (fun x => f (c • x)) z = c ^ 2 * m60AreaDensity g f (c • z) := by
  unfold m60AreaDensity
  rw [m60AreaGram_comp_smul, Matrix.det_smul]
  simp only [Fintype.card_fin]
  rw [max_eq_right (mul_nonneg (sq_nonneg _) (m60AreaGram_det_nonneg g f (c • z))),
    max_eq_right (m60AreaGram_det_nonneg g f (c • z)),
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg c)]

theorem m60AreaIntegral_comp_smul (g : RiemannianMetric n M)
    (f : LoopPlane → M) {c : ℝ} (hc : 0 < c) (S : Set LoopPlane) :
    (∫ z in S, m60AreaDensity g (fun x => f (c • x)) z ∂volume) =
      ∫ z in c • S, m60AreaDensity g f z ∂volume := by
  simp_rw [m60AreaDensity_comp_smul]
  rw [integral_const_mul, Measure.setIntegral_comp_smul_of_pos volume _ S hc]
  have hdim : Module.finrank ℝ LoopPlane = 2 := by simp [LoopPlane]
  rw [hdim, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hc.ne'), one_mul]

theorem m60AreaIntegral_rescaled_disk (g : RiemannianMetric n M)
    (f : LoopPlane → M) {r : ℝ} (hr : 0 < r) :
    (∫ z in Metric.closedBall (0 : LoopPlane) r,
      m60AreaDensity g (fun x => f (r⁻¹ • x)) z ∂volume) =
        ∫ z in loopDiskSet, m60AreaDensity g f z ∂volume := by
  rw [m60AreaIntegral_comp_smul g f (inv_pos.mpr hr)]
  congr 1
  rw [smul_closedBall' (inv_ne_zero hr.ne'), smul_zero, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
  rfl

theorem m60_inv_smul_closedBall {r : ℝ} (hr : 0 < r) :
    r⁻¹ • Metric.closedBall (0 : LoopPlane) r = loopDiskSet := by
  rw [smul_closedBall' (inv_ne_zero hr.ne'), smul_zero, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
  rfl

theorem m60AreaDensity_integrableOn_comp_smul (g : RiemannianMetric n M)
    (f : LoopPlane → M) {c : ℝ} (hc : c ≠ 0) (S : Set LoopPlane)
    (hf : IntegrableOn (m60AreaDensity g f) (c • S) volume) :
    IntegrableOn (m60AreaDensity g (fun x => f (c • x))) S volume := by
  have hi := (M60.integrableOn_comp_smul_iff volume (m60AreaDensity g f) S hc).mpr hf
  change Integrable (fun z => m60AreaDensity g (fun x => f (c • x)) z) (volume.restrict S)
  simp_rw [m60AreaDensity_comp_smul]
  exact hi.const_mul (c ^ 2)

omit [IsManifold (𝓡 n) ∞ M] in

theorem m60_ae_mdifferentiable_comp_smul (f : LoopPlane → M)
    {c : ℝ} (hc : c ≠ 0) (S : Set LoopPlane)
    (hf : ∀ᵐ z ∂volume, z ∈ c • S → MDifferentiableAt (𝓡 2) (𝓡 n) f z) :
    ∀ᵐ z ∂volume, z ∈ S →
      MDifferentiableAt (𝓡 2) (𝓡 n) (fun x => f (c • x)) z := by
  filter_upwards [M60.ae_comp_smul volume hf hc] with z hz hS
  exact (hz (smul_mem_smul_set hS)).comp z
    (((hasFDerivAt_id z).const_smul c).hasMFDerivAt.mdifferentiableAt)

end PoincareConjecture
