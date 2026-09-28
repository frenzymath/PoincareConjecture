import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.EpsilonRegularity
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.DiskRescaling
import Mathlib.Analysis.Calculus.FDeriv.Equiv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology Manifold ContDiff Pointwise

noncomputable section

universe u

namespace PoincareConjecture.M60

theorem suRescale_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : LoopPlane → E) (a : LoopPlane) (s : ℝ) (z : LoopPlane) :
    fderiv ℝ (fun y => u (a + s • y)) z = s • fderiv ℝ u (a + s • z) := by
  change fderiv ℝ (fun y => (fun w => u (a + w)) (s • y)) z = _
  rw [fderiv_comp_smul (f := fun w => u (a + w)) s, fderiv_comp_add_left]

theorem suRescale_second_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : LoopPlane → E) (a : LoopPlane) (s : ℝ) (z v w : LoopPlane) :
    fderiv ℝ (fun y => fderiv ℝ (fun x => u (a + s • x)) y v) z w =
      s ^ 2 • fderiv ℝ (fun y => fderiv ℝ u y v) (a + s • z) w := by
  simp_rw [suRescale_fderiv, smul_apply]
  change fderiv ℝ (s • (fun y => fderiv ℝ u (a + s • y) v)) z w = _
  rw [fderiv_const_smul_field, Pi.smul_apply,
    suRescale_fderiv (fun y => fderiv ℝ u y v) a s z]
  simp only [smul_apply, smul_smul, pow_two]

theorem suRescale_closedBall (a : LoopPlane) {s : ℝ} (hs : 0 < s) (R : ℝ) :
    (fun z : LoopPlane => a + s • z) '' Metric.closedBall 0 R =
      Metric.closedBall a (s * R) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hs.le]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw) hs.le
  · intro hz
    refine ⟨s⁻¹ • (z - a), ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
      have h := mul_le_mul_of_nonneg_left
        (show ‖z - a‖ ≤ s * R by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz)
        (inv_nonneg.mpr hs.le)
      simpa only [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul] using h
    · change a + s • (s⁻¹ • (z - a)) = z
      rw [smul_inv_smul₀ hs.ne']
      abel

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in

theorem suRescale_mfderiv (f : LoopPlane → M)
    (hf : MDifferentiable (𝓡 2) (𝓡 n) f) (a : LoopPlane) (s : ℝ) (z : LoopPlane) :
    mfderiv (𝓡 2) (𝓡 n) (fun y => f (a + s • y)) z =
      s • mfderiv (𝓡 2) (𝓡 n) f (a + s • z) := by
  have hA : HasMFDerivAt (𝓡 2) (𝓡 2) (fun y : LoopPlane => a + s • y) z
      (s • ContinuousLinearMap.id ℝ LoopPlane) :=
    (((hasFDerivAt_id z).const_smul s).const_add a).hasMFDerivAt
  change mfderiv (𝓡 2) (𝓡 n) (f ∘ (fun y => a + s • y)) z = _
  rw [mfderiv_comp z (hf _) hA.mdifferentiableAt, hA.mfderiv]
  ext v
  simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul]
  rfl

theorem suRescale_areaGram (g : RiemannianMetric n M) (f : LoopPlane → M)
    (hf : MDifferentiable (𝓡 2) (𝓡 n) f) (a : LoopPlane) (s : ℝ) (z : LoopPlane) :
    m60AreaGram g (fun y => f (a + s • y)) z = s ^ 2 • m60AreaGram g f (a + s • z) := by
  ext i j
  simp only [m60AreaGram, suRescale_mfderiv f hf, smul_apply,
    Matrix.smul_apply, smul_eq_mul, map_smul]
  ring_nf
  rfl

theorem suRescale_energyDensity (g : RiemannianMetric n M) (f : LoopPlane → M)
    (hf : MDifferentiable (𝓡 2) (𝓡 n) f) (a : LoopPlane) (s : ℝ) (z : LoopPlane) :
    m60EnergyDensity g (fun y => f (a + s • y)) z =
      s ^ 2 * m60EnergyDensity g f (a + s • z) := by
  unfold m60EnergyDensity
  rw [suRescale_areaGram g f hf]
  simp only [Matrix.trace_smul, smul_eq_mul]
  ring

theorem suRescale_areaDensity (g : RiemannianMetric n M) (f : LoopPlane → M)
    (hf : MDifferentiable (𝓡 2) (𝓡 n) f) (a : LoopPlane) (s : ℝ) (z : LoopPlane) :
    m60AreaDensity g (fun y => f (a + s • y)) z =
      s ^ 2 * m60AreaDensity g f (a + s • z) := by
  unfold m60AreaDensity
  rw [suRescale_areaGram g f hf, Matrix.det_smul]
  simp only [Fintype.card_fin]
  rw [max_eq_right (mul_nonneg (sq_nonneg _) (m60AreaGram_det_nonneg g f (a + s • z))),
    max_eq_right (m60AreaGram_det_nonneg g f (a + s • z)),
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg s)]

theorem suRescale_integral (F : LoopPlane → ℝ) (a : LoopPlane)
    {s : ℝ} (hs : 0 < s) (S : Set LoopPlane) :
    (∫ z in S, s ^ 2 * F (a + s • z)) =
      ∫ z in (fun w => a + s • w) '' S, F z := by
  rw [integral_const_mul,
    Measure.setIntegral_comp_smul_of_pos volume (fun w => F (a + w)) S hs]
  have hdim : Module.finrank ℝ LoopPlane = 2 := by simp [LoopPlane]
  rw [hdim, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hs.ne'), one_mul]
  have ht := (measurePreserving_add_left (volume : Measure LoopPlane) a).setIntegral_image_emb
    (MeasurableEquiv.addLeft a).measurableEmbedding F (s • S)
  have hset : (fun x : LoopPlane => a + x) '' (s • S) =
      (fun w => a + s • w) '' S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨v, hv, rfl⟩ := hw
      exact ⟨v, hv, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨s • w, ⟨w, hw, rfl⟩, rfl⟩
  rw [← ht, hset]

theorem suRescale_energyIntegral (g : RiemannianMetric n M) (f : LoopPlane → M)
    (hf : MDifferentiable (𝓡 2) (𝓡 n) f) (a : LoopPlane) {s : ℝ} (hs : 0 < s)
    (S : Set LoopPlane) :
    (∫ z in S, m60EnergyDensity g (fun y => f (a + s • y)) z) =
      ∫ z in (fun w => a + s • w) '' S, m60EnergyDensity g f z := by
  simp_rw [suRescale_energyDensity g f hf]
  exact suRescale_integral _ a hs S

theorem suRescale_areaIntegral (g : RiemannianMetric n M) (f : LoopPlane → M)
    (hf : MDifferentiable (𝓡 2) (𝓡 n) f) (a : LoopPlane) {s : ℝ} (hs : 0 < s)
    (S : Set LoopPlane) :
    (∫ z in S, m60AreaDensity g (fun y => f (a + s • y)) z) =
      ∫ z in (fun w => a + s • w) '' S, m60AreaDensity g f z := by
  simp_rw [suRescale_areaDensity g f hf]
  exact suRescale_integral _ a hs S

theorem suRescale_covDerivAlong
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Gamma : E → E →L[ℝ] E →L[ℝ] E) (u V : LoopPlane → E)
    (a : LoopPlane) (s t : ℝ) (z d : LoopPlane) :
    ConnectionVariation.covDerivAlong Gamma (fun y => u (a + s • y))
      (fun y => t • V (a + s • y)) d z =
        (s * t) • ConnectionVariation.covDerivAlong Gamma u V d (a + s • z) := by
  unfold ConnectionVariation.covDerivAlong
  rw [suRescale_fderiv]
  have hd : fderiv ℝ (fun y => t • V (a + s • y)) z =
      t • (s • fderiv ℝ V (a + s • z)) := by
    change fderiv ℝ (t • (fun y => V (a + s • y))) z = _
    rw [fderiv_const_smul_field, Pi.smul_apply, suRescale_fderiv]
  rw [hd]
  simp only [smul_apply, map_smul, smul_add, smul_smul]
  module

theorem suRescale_weightedEuler
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Gamma : E → E →L[ℝ] E →L[ℝ] E) (u : LoopPlane → E)
    (q : LoopPlane → ℝ) (hq : ∀ x, 0 ≤ q x)
    (a : LoopPlane) (s rho alpha : ℝ) (z : LoopPlane) :
    (∑ i : Fin 2, ConnectionVariation.covDerivAlong Gamma (fun y => u (a + s • y))
      (fun y => ((s * rho) ^ 2 + s ^ 2 * q (a + s • y)) ^ (alpha - 1) •
        fderiv ℝ (fun w => u (a + s • w)) y (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) z) =
      (s ^ 2 * (s ^ 2) ^ (alpha - 1)) •
        ∑ i : Fin 2, ConnectionVariation.covDerivAlong Gamma u
          (fun y => (rho ^ 2 + q y) ^ (alpha - 1) •
            fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
              (EuclideanSpace.basisFun (Fin 2) ℝ i) (a + s • z) := by
  have hflux (i : Fin 2) :
      (fun y => ((s * rho) ^ 2 + s ^ 2 * q (a + s • y)) ^ (alpha - 1) •
        fderiv ℝ (fun w => u (a + s • w)) y (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      (fun y => (s * (s ^ 2) ^ (alpha - 1)) •
        ((rho ^ 2 + q (a + s • y)) ^ (alpha - 1) •
          fderiv ℝ u (a + s • y) (EuclideanSpace.basisFun (Fin 2) ℝ i))) := by
    funext y
    rw [suRescale_fderiv]
    have hbase : (s * rho) ^ 2 + s ^ 2 * q (a + s • y) =
        s ^ 2 * (rho ^ 2 + q (a + s • y)) := by ring
    rw [hbase, Real.mul_rpow (sq_nonneg s) (add_nonneg (sq_nonneg rho) (hq _))]
    simp only [smul_apply, smul_smul]
    congr 1
    ring
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hflux i]
  have h := suRescale_covDerivAlong Gamma u
    (fun y => (rho ^ 2 + q y) ^ (alpha - 1) •
      fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
    a s (s * (s ^ 2) ^ (alpha - 1)) z (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hc : s * (s * (s ^ 2) ^ (alpha - 1)) = s ^ 2 * (s ^ 2) ^ (alpha - 1) := by ring
  rw [hc] at h
  exact h

end PoincareConjecture.M60

end
