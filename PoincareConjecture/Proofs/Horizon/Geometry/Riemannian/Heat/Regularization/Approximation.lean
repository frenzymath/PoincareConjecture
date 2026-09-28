import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Product
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Regularity
import Mathlib.MeasureTheory.Integral.DominatedConvergence














set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M}



theorem exists_compact_distance_approximations (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (O : M) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (happrox : ∀ x, |f x - (g.edist O x).toReal| ≤ 1)
    (hgrad : ∀ x, g.tangentNorm x (D.gradient f x) ≤ 2) :
    ∃ u : ℕ → M → ℝ,
      (∀ j, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (u j)) ∧
      (∀ j, HasCompactSupport (u j)) ∧
      (∀ j x, |u j x| ≤ |f x|) ∧
      (∀ j x, g.tangentNorm x (D.gradient (u j) x) ≤ 2 + 6 * heatCutoffConstant) ∧
      (∀ x, ∀ᶠ j in atTop, u j =ᶠ[𝓝 x] f) := by
  classical
  have hcut (j : ℕ) := D.exists_distance_cutoff hcomplete O hf happrox hgrad
    (R := (j : ℝ) + 1) (by linarith [Nat.cast_nonneg (α := ℝ) j])
  choose η hη hcompact hηrange hηone hηsupport hηgrad using hcut
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  refine ⟨fun j x ↦ η j x * f x, fun j ↦ (hη j).mul hf,
    fun j ↦ (hcompact j).mul_right, ?_, ?_, ?_⟩
  · intro j x
    rw [abs_mul, abs_of_nonneg (hηrange j x).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (hηrange j x).2
  · intro j x
    rw [D.gradient_mul ((hη j x).mdifferentiableAt (by simp))
      ((hf x).mdifferentiableAt (by simp))]
    change ‖η j x • D.gradient f x + f x • D.gradient (η j) x‖ ≤ _
    have hfirst : ‖η j x • D.gradient f x‖ ≤ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hηrange j x).1]
      exact (mul_le_mul (hηrange j x).2 (hgrad x) (Real.sqrt_nonneg _) zero_le_one).trans_eq
        (one_mul _)
    have hsecond : ‖f x • D.gradient (η j) x‖ ≤ 6 * heatCutoffConstant := by
      by_cases hx : x ∈ tsupport (η j)
      · have hfx : |f x| ≤ 6 * ((j : ℝ) + 1) := by
          have habs := abs_add_le (f x - (g.edist O x).toReal) (g.edist O x).toReal
          rw [sub_add_cancel, abs_of_nonneg ENNReal.toReal_nonneg] at habs
          have hs := hηsupport j hx
          change (g.edist O x).toReal ≤ 5 * ((j : ℝ) + 1) at hs
          have ha := happrox x
          linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
        rw [norm_smul, Real.norm_eq_abs]
        calc
          _ ≤ (6 * ((j : ℝ) + 1)) * (heatCutoffConstant / ((j : ℝ) + 1)) :=
            mul_le_mul hfx (hηgrad j x) (Real.sqrt_nonneg _) (by positivity)
          _ = 6 * heatCutoffConstant := by field_simp
      · rw [D.gradient_eq_zero_of_notMem_tsupport hx, smul_zero, norm_zero]
        exact mul_nonneg (by norm_num) heatCutoffConstant_pos.le
    exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)
  · intro x
    obtain ⟨N, hN⟩ := exists_nat_gt ((g.edist O x).toReal + 1)
    filter_upwards [eventually_ge_atTop N] with j hj
    have hU : {y | (g.edist O y).toReal < (g.edist O x).toReal + 1} ∈ 𝓝 x :=
      (g.continuous_toReal_edist O).continuousAt.preimage_mem_nhds
        (Iio_mem_nhds (by linarith))
    filter_upwards [hU] with y hy
    rw [hηone j y (by
      have hj' : (N : ℝ) ≤ j := by exact_mod_cast hj
      linarith), one_mul]

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem tendsto_integral_abs_approximation_error
    (H : ConservativeHeatKernelData g) {f : M → ℝ} (hf : Continuous f)
    {L : ℝ} (hLip : ∀ x y, |f y - f x| ≤ L * (g.edist x y).toReal)
    {u : ℕ → M → ℝ} (hu : ∀ j, Continuous (u j))
    (hbound : ∀ j x, |u j x| ≤ |f x|)
    (hlim : ∀ x, Tendsto (fun j ↦ u j x) atTop (𝓝 (f x)))
    (x : M) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun j ↦ ∫ y, |u j y - f y| * H.kernel x y t ∂g.volumeMeasure)
      atTop (𝓝 0) := by
  have hk := H.integrable_kernel x ht
  have hi := H.integrable_weighted_of_distance_lipschitz hf hLip x ht
  have hmajor : Integrable (fun y ↦ 2 * |f y * H.kernel x y t|) g.volumeMeasure :=
    hi.norm.const_mul 2
  have h := tendsto_integral_of_dominated_convergence (f := fun _ ↦ (0 : ℝ))
    (fun y ↦ 2 * |f y * H.kernel x y t|)
    (fun j ↦ ((hu j).sub hf).abs.aestronglyMeasurable.mul hk.aestronglyMeasurable)
    hmajor ?_ ?_
  · simpa using h
  · intro j
    filter_upwards [] with y
    change ‖|u j y - f y| * H.kernel x y t‖ ≤ 2 * |f y * H.kernel x y t|
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_mul, abs_of_pos (H.positive x y t ht)]
    have he : |u j y - f y| ≤ 2 * |f y| := by
      calc
        _ ≤ |u j y| + |f y| := abs_sub _ _
        _ ≤ 2 * |f y| := by linarith [hbound j y]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right he (H.positive x y t ht).le
  · filter_upwards [] with y
    simpa using ((hlim y).sub_const (f y)).abs.mul_const (H.kernel x y t)



theorem exists_compact_kernel_approximations [PreconnectedSpace M]
    (H : ConservativeHeatKernelData g) (hcomplete : MetricComplete g) (O : M)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (happrox : ∀ x, |f x - (g.edist O x).toReal| ≤ 1)
    (hgrad : ∀ x, g.tangentNorm x (H.connection.gradient f x) ≤ 2) :
    ∃ u : ℕ → M → ℝ,
      (∀ j, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (u j)) ∧
      (∀ j, HasCompactSupport (u j)) ∧
      (∀ j x, |u j x| ≤ |f x|) ∧
      (∀ j x, g.tangentNorm x (H.connection.gradient (u j) x) ≤
        2 + 6 * heatCutoffConstant) ∧
      (∀ x, ∀ᶠ j in atTop, u j =ᶠ[𝓝 x] f) ∧
      (∀ x, ∀ᶠ j in atTop, H.connection.gradient (u j) x = H.connection.gradient f x) ∧
      (∀ x t, 0 < t →
        Tendsto (fun j ↦ ∫ y, |u j y - f y| * H.kernel x y t ∂g.volumeMeasure)
          atTop (𝓝 0)) := by
  obtain ⟨u, hu, hc, hb, hg, he⟩ :=
    H.connection.exists_compact_distance_approximations hcomplete O hf happrox hgrad
  refine ⟨u, hu, hc, hb, hg, he, ?_, ?_⟩
  · intro x
    filter_upwards [he x] with j hj
    simp only [LeviCivitaData.gradient, Poincare.mvfderiv_eq_of_eventuallyEq hj]
  · intro x t ht
    have hLip : ∀ x y, |f y - f x| ≤ 2 * (g.edist x y).toReal := by
      intro x y
      rw [abs_sub_comm]
      exact g.abs_sub_le_mul_toReal_edist_of_derivative_bound (K := 2)
        (hf.of_le (by simp)) (by norm_num)
        (fun z v ↦ (H.connection.gradient_norm_le_iff f z (by norm_num)).mp (hgrad z) v)
        x y
    apply H.tendsto_integral_abs_approximation_error hf.continuous hLip
      (fun j ↦ (hu j).continuous) hb ?_ x ht
    intro y
    apply tendsto_const_nhds.congr'
    filter_upwards [he y] with j hj
    exact hj.self_of_nhds.symm

end PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData
