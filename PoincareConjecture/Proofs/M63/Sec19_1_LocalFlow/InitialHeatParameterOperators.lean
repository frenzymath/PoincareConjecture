import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialResponseTrace

set_option autoImplicit false

open Set Filter MeasureTheory

namespace PoincareConjecture.M63

open SpectralHeatNative QuasilinearDeTurckNative

variable {iota : Type*} (lambda : iota → NNReal) {T : ℝ}

theorem exists_initialHeatPath_operator [Countable iota] (_hT : 0 ≤ T) :
    ∃ V : State iota →L[ℝ] ResponsePath iota T, ‖V‖ ≤ 1 ∧
      ∀ w (t : Icc (0 : ℝ) T), V w t = heat lambda (t : ℝ).toNNReal w := by
  let V0 (w : State iota) : ResponsePath iota T :=
    ⟨fun t => heat lambda (t : ℝ).toNNReal w,
      (continuous_heat_apply lambda w).comp
        (continuous_real_toNNReal.comp continuous_subtype_val)⟩
  let V1 : State iota →ₗ[ℝ] ResponsePath iota T :=
    { toFun := V0
      map_add' := by
        intro u v
        apply ContinuousMap.ext
        intro t
        exact (heat lambda (t : ℝ).toNNReal).map_add u v
      map_smul' := by
        intro c w
        apply ContinuousMap.ext
        intro t
        exact (heat lambda (t : ℝ).toNNReal).map_smul c w }
  have hnorm (w : State iota) : ‖V1 w‖ ≤ 1 * ‖w‖ := by
    rw [one_mul]
    exact (ContinuousMap.norm_le _ (norm_nonneg w)).mpr
      (fun t => norm_heat_apply_le lambda (t : ℝ).toNNReal w)
  let V := V1.mkContinuous 1 hnorm
  exact ⟨V, ContinuousLinearMap.opNorm_le_bound _ zero_le_one hnorm, fun _ _ => rfl⟩

theorem exists_initialHeatHigh_operator [Countable iota] (hT : 0 ≤ T) :
    ∃ P : State iota →L[ℝ] ForcingSpace iota T, ‖P‖ ≤ Real.sqrt (2 * T + 1) ∧
      ∀ w, ∀ᵐ t ∂timeMeasure T, P w t = initialHeatHigh lambda w t := by
  have hmem (w : State iota) := (initialHeatHigh_memLp_energy lambda w hT).1
  let P0 (w : State iota) : ForcingSpace iota T := (hmem w).toLp (initialHeatHigh lambda w)
  have hP0 (w : State iota) : ∀ᵐ t ∂timeMeasure T, P0 w t = initialHeatHigh lambda w t :=
    (hmem w).coeFn_toLp
  have hadd (u v : State iota) : P0 (u + v) = P0 u + P0 v := by
    apply Lp.ext
    filter_upwards [hP0 (u + v), hP0 u, hP0 v, Lp.coeFn_add (P0 u) (P0 v),
      ae_restrict_mem measurableSet_Ioc] with t huv hu hv hsum ht
    rw [huv, hsum, Pi.add_apply, hu, hv]
    simp only [initialHeatHigh, initialHeatGenerator_eq lambda _ ht.1, map_add]
    abel
  have hsmul (c : ℝ) (w : State iota) : P0 (c • w) = c • P0 w := by
    apply Lp.ext
    filter_upwards [hP0 (c • w), hP0 w, Lp.coeFn_smul c (P0 w),
      ae_restrict_mem measurableSet_Ioc] with t hcw hw hscale ht
    rw [hcw, hscale, Pi.smul_apply, hw]
    simp only [initialHeatHigh, initialHeatGenerator_eq lambda _ ht.1, map_smul, smul_add]
  let P1 : State iota →ₗ[ℝ] ForcingSpace iota T :=
    { toFun := P0
      map_add' := hadd
      map_smul' := hsmul }
  have hnorm (w : State iota) : ‖P1 w‖ ≤ Real.sqrt (2 * T + 1) * ‖w‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    calc
      ‖P1 w‖ ^ 2 = ∫ t, ‖initialHeatHigh lambda w t‖ ^ 2 ∂timeMeasure T := norm_toLp_sq (hmem w)
      _ ≤ (2 * T + 1) * ‖w‖ ^ 2 := (initialHeatHigh_memLp_energy lambda w hT).2
      _ = (Real.sqrt (2 * T + 1) * ‖w‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 2 * T + 1)]
  let P := P1.mkContinuous (Real.sqrt (2 * T + 1)) hnorm
  exact ⟨P, ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) hnorm, hP0⟩

end PoincareConjecture.M63
