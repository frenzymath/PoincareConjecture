import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.Approximation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Lipschitz












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M}



theorem gradient_norm_le_of_tendsto (D : LeviCivitaData g)
    {ι : Type*} {l : Filter ι} [l.NeBot] {u : ι → M → ℝ} {f : M → ℝ}
    {C : ℝ≥0} (hC : 0 < C)
    (hu : ∀ᶠ i in l, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 (u i))
    (hgrad : ∀ᶠ i in l, ∀ x, g.tangentNorm x (D.gradient (u i) x) ≤ C)
    (hlim : ∀ x, Tendsto (fun i => u i x) l (𝓝 (f x)))
    {x : M} (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x) :
    g.tangentNorm x (D.gradient f x) ≤ C := by
  apply D.gradient_norm_le_of_distance_lipschitz C.coe_nonneg _ hf
  intro x y
  apply le_of_tendsto ((hlim x).sub (hlim y)).abs
  filter_upwards [hu, hgrad] with i hi hgi
  exact g.abs_sub_le_mul_toReal_edist_of_derivative_bound hi hC
    (fun z => (D.gradient_norm_le_iff (u i) z C.coe_nonneg).mp (hgi z)) x y

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem tendsto_integral_of_dominated_initial_approximations
    (H : ConservativeHeatKernelData g) {f : M → ℝ} (hf : Continuous f)
    {L : ℝ} (hLip : ∀ x y, |f y - f x| ≤ L * (g.edist x y).toReal)
    {u : ℕ → M → ℝ} (hu : ∀ j, Continuous (u j))
    (hb : ∀ j x, |u j x| ≤ |f x|)
    (hl : ∀ x, Tendsto (fun j => u j x) atTop (𝓝 (f x)))
    (x : M) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun j => ∫ y, u j y * H.kernel x y t ∂g.volumeMeasure) atTop
      (𝓝 (∫ y, f y * H.kernel x y t ∂g.volumeMeasure)) := by
  have hk := H.integrable_kernel x ht
  apply tendsto_integral_of_dominated_convergence (fun y => |f y * H.kernel x y t|)
    (fun j => (hu j).aestronglyMeasurable.mul hk.aestronglyMeasurable)
    (H.integrable_weighted_of_distance_lipschitz hf hLip x ht).norm
  · intro j
    filter_upwards [] with y
    simpa only [Real.norm_eq_abs, Pi.mul_apply, abs_mul] using
      mul_le_mul_of_nonneg_right (hb j y) (abs_nonneg (H.kernel x y t))
  · filter_upwards [] with y
    exact (hl y).mul_const (H.kernel x y t)



theorem kernel_integral_gradient_bound_of_compact_evolutions [PreconnectedSpace M]
    (H : ConservativeHeatKernelData g) (hcomplete : MetricComplete g) (O : M)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (happrox : ∀ x, |f x - (g.edist O x).toReal| ≤ 1)
    (hgrad : ∀ x, g.tangentNorm x (H.connection.gradient f x) ≤ 2)
    {C : ℝ≥0} (hC : 0 < C) {t : ℝ} (ht : 0 < t)
    (hcompact : ∀ u : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u →
      HasCompactSupport u →
      (∀ x, g.tangentNorm x (H.connection.gradient u x) ≤ 2 + 6 * heatCutoffConstant) →
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1
        (fun x => ∫ y, u y * H.kernel x y t ∂g.volumeMeasure) ∧
      ∀ x, g.tangentNorm x (H.connection.gradient
        (fun z => ∫ y, u y * H.kernel z y t ∂g.volumeMeasure) x) ≤ C)
    {x : M} (hF : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun z => ∫ y, f y * H.kernel z y t ∂g.volumeMeasure) x) :
    g.tangentNorm x (H.connection.gradient
      (fun z => ∫ y, f y * H.kernel z y t ∂g.volumeMeasure) x) ≤ C := by
  obtain ⟨u, hu, hc, hb, hg, he⟩ :=
    H.connection.exists_compact_distance_approximations hcomplete O hf happrox hgrad
  have hLip : ∀ x y, |f y - f x| ≤ 2 * (g.edist x y).toReal := by
    intro x y
    rw [abs_sub_comm]
    exact g.abs_sub_le_mul_toReal_edist_of_derivative_bound
      (hf.of_le (by simp)) (K := 2) (by norm_num)
      (fun z => (H.connection.gradient_norm_le_iff f z (by norm_num)).mp (hgrad z)) x y
  apply H.connection.gradient_norm_le_of_tendsto (l := atTop)
    (u := fun j z => ∫ y, u j y * H.kernel z y t ∂g.volumeMeasure) hC
    (Eventually.of_forall (fun j => (hcompact (u j) (hu j) (hc j) (hg j)).1))
    (Eventually.of_forall (fun j => (hcompact (u j) (hu j) (hc j) (hg j)).2)) _ hF
  intro z
  apply H.tendsto_integral_of_dominated_initial_approximations hf.continuous hLip
    (fun j => (hu j).continuous) hb _ z ht
  intro y
  apply tendsto_const_nhds.congr'
  filter_upwards [he y] with j hj
  exact hj.self_of_nhds.symm

end PoincareConjecture.RiemannianMetric.ConservativeHeatKernelData
