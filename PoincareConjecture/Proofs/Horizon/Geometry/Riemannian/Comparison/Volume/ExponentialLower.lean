import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.DensityBound

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem inv_factorial_mul_pow_le_pullbackVolumeDensity
    (g : RiemannianMetric n M) {f : EuclideanSpace ℝ (Fin n) → M}
    {x : EuclideanSpace ℝ (Fin n)} {C : ℝ} (hC : 0 < C)
    (hi : Injective (mfderiv (𝓡 n) (𝓡 n) f x))
    (hbound : ∀ w : EuclideanSpace ℝ (Fin n),
      ‖w‖ ≤ C * g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x w)) :
    ((n.factorial : ℝ) * C ^ n)⁻¹ ≤ g.pullbackVolumeDensity f x := by
  obtain ⟨A, hA, hdet⟩ := g.exists_frozenPullbackEquiv hi
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hentry (i j : Fin n) :
      |LinearMap.toMatrix b.toBasis b.toBasis A.symm.toContinuousLinearMap.toLinearMap i j| ≤ C := by
    rw [LinearMap.toMatrix_apply]
    change |(A.symm (b j)) i| ≤ C
    calc
      |(A.symm (b j)) i| ≤ ‖A.symm (b j)‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (A.symm (b j)) i
      _ ≤ C * g.tangentNorm (f x)
          (mfderiv (𝓡 n) (𝓡 n) f x (A.symm (b j))) := hbound _
      _ = C * ‖b j‖ := by rw [← hA, A.apply_symm_apply]
      _ = C := by simp [b, EuclideanSpace.basisFun_apply]
  have hinv := Matrix.det_le (abv := AbsoluteValue.abs) hentry
  rw [LinearMap.det_toMatrix] at hinv
  change |A.symm.toContinuousLinearMap.det| ≤ _ at hinv
  have hinv' : |A.symm.toContinuousLinearMap.det| ≤ (n.factorial : ℝ) * C ^ n := by
    simpa only [Fintype.card_fin, nsmul_eq_mul] using hinv
  have hproduct : |A.symm.toContinuousLinearMap.det| * |A.toContinuousLinearMap.det| = 1 := by
    rw [← abs_mul]
    change |A.toLinearEquiv.symm.toLinearMap.det * A.toLinearEquiv.toLinearMap.det| = 1
    rw [A.toLinearEquiv.det_symm_mul_det, abs_one]
  have hpositive : 0 < (n.factorial : ℝ) * C ^ n := by positivity
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hpositive).mpr
  rw [← hdet]
  nlinarith [mul_le_mul_of_nonneg_right hinv' (abs_nonneg A.toContinuousLinearMap.det)]

theorem density_mul_volume_le_volumeMeasure_image_of_differential_lower_bound
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    (g : RiemannianMetric n M) {f : EuclideanSpace ℝ (Fin n) → M}
    {U : Set (EuclideanSpace ℝ (Fin n))} {C : ℝ} (hC : 0 < C)
    (hU : MeasurableSet U) (hf : ∀ x ∈ U, MDifferentiableAt (𝓡 n) (𝓡 n) f x)
    (hinj : InjOn f U)
    (hderiv : ∀ x ∈ U, Injective (mfderiv (𝓡 n) (𝓡 n) f x))
    (hbound : ∀ x ∈ U, ∀ w : EuclideanSpace ℝ (Fin n),
      ‖w‖ ≤ C * g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x w)) :
    ENNReal.ofReal (((n.factorial : ℝ) * C ^ n)⁻¹) * volume U ≤
      g.volumeMeasure (f '' U) := by
  rw [g.volumeMeasure_image_eq_lintegral_of_mdifferentiableAt_injOn hU hf hinj]
  calc
    _ = ∫⁻ _ in U, ENNReal.ofReal (((n.factorial : ℝ) * C ^ n)⁻¹) := by simp
    _ ≤ _ := setLIntegral_mono' hU fun x hx => ENNReal.ofReal_le_ofReal
      (g.inv_factorial_mul_pow_le_pullbackVolumeDensity hC (hderiv x hx) (hbound x hx))

theorem ball_volume_lower_bound_of_injective_exponential
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    (g : RiemannianMetric n M) (p : M)
    {e : EuclideanSpace ℝ (Fin n) → M} {r R : ℝ}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 r))
    (hinj : InjOn e (Metric.ball 0 r))
    (hmaps : MapsTo e (Metric.ball 0 r) (g.ball p R))
    (hlower : ∀ x ∈ Metric.ball 0 r, ∀ w : EuclideanSpace ℝ (Fin n),
      ‖w‖ / 2 ≤ g.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x w)) :
    ENNReal.ofReal (((n.factorial : ℝ) * (2 : ℝ) ^ n)⁻¹) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) ≤
      g.volumeMeasure (g.ball p R) := by
  refine (g.density_mul_volume_le_volumeMeasure_image_of_differential_lower_bound
    (by norm_num : (0 : ℝ) < 2) Metric.isOpen_ball.measurableSet
    (fun x hx => (he.contMDiffAt (Metric.isOpen_ball.mem_nhds hx)).mdifferentiableAt
      (by simp)) hinj
    (fun x hx => (g.bijective_mfderiv_of_tangentNorm_lower_bound x (hlower x hx)).1)
    (fun x hx w => by linarith [hlower x hx w])).trans ?_
  exact measure_mono (image_subset_iff.mpr hmaps)

end PoincareConjecture.RiemannianMetric
