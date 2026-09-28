import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.TimeComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.Cutoff
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.NoncompactEnergy










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Analysis.Heat



theorem ae_eq_zero_of_cutoff_integral_tendsto_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {q : α → ℝ} (hq : 0 ≤ᵐ[μ] q) (hqm : AEMeasurable q μ)
    {χ : ℕ → α → ℝ} (hχm : ∀ j, AEMeasurable (χ j) μ)
    (hχ0 : ∀ j, 0 ≤ᵐ[μ] χ j)
    (hχlim : ∀ᵐ x ∂μ, Tendsto (fun j ↦ χ j x) atTop (𝓝 1))
    (hi : ∀ j, Integrable (fun x ↦ χ j x * q x) μ)
    (hz : Tendsto (fun j ↦ ∫ x, χ j x * q x ∂μ) atTop (𝓝 0)) :
    q =ᵐ[μ] 0 := by
  have hpoint : ∀ᵐ x ∂μ, ENNReal.ofReal (q x) =
      liminf (fun j ↦ ENNReal.ofReal (χ j x * q x)) atTop := by
    filter_upwards [hχlim] with x hx
    have ht : Tendsto (fun j ↦ χ j x * q x) atTop (𝓝 (q x)) := by
      simpa using hx.mul_const (q x)
    exact ((ENNReal.continuous_ofReal.tendsto _).comp ht).liminf_eq.symm
  have hfatou : (∫⁻ x, ENNReal.ofReal (q x) ∂μ) ≤
      liminf (fun j ↦ ∫⁻ x, ENNReal.ofReal (χ j x * q x) ∂μ) atTop := by
    rw [lintegral_congr_ae hpoint]
    exact lintegral_liminf_le' (fun j ↦ ((hχm j).mul hqm).ennreal_ofReal)
  have heq (j : ℕ) : (∫⁻ x, ENNReal.ofReal (χ j x * q x) ∂μ) =
      ENNReal.ofReal (∫ x, χ j x * q x ∂μ) := by
    apply (ofReal_integral_eq_lintegral_ofReal (hi j) ?_).symm
    filter_upwards [hχ0 j, hq] with x hx hqx
    exact mul_nonneg hx hqx
  simp_rw [heq] at hfatou
  have ht := (ENNReal.continuous_ofReal.tendsto 0).comp hz
  simp only [Function.comp_def] at ht
  rw [ht.liminf_eq, ENNReal.ofReal_zero] at hfatou
  have hzero := (lintegral_eq_zero_iff' hqm.ennreal_ofReal).mp (le_antisymm hfatou bot_le)
  filter_upwards [hzero, hq] with x hx hqx
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp hx) hqx

end Poincare.Analysis.Heat

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [PreconnectedSpace M]
  {g : RiemannianMetric n M}



theorem weighted_cutoff_boundary_le (D : LeviCivitaData g)
    {u ξ : ℝ × M → ℝ} {a b B : ℝ} (hab : a ≤ b)
    (huc : ContinuousOn u (Icc a b ×ˢ univ))
    (hξc : ContinuousOn ξ (Icc a b ×ˢ univ))
    (hi : Integrable (fun p : ℝ × M ↦ Real.exp (ξ p) * u p ^ 2)
      ((volume.restrict (Ioc a b)).prod g.volumeMeasure))
    {η : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hηc : HasCompactSupport η)
    (hgrad : ∀ x, g.inner x (D.gradient η x) (D.gradient η x) ≤ B) :
    (∫ t in a..b, ∫ x, Real.exp (ξ (t, x)) * u (t, x) ^ 2 *
      g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure) ≤
      B * ∫ p : ℝ × M, Real.exp (ξ p) * u p ^ 2
        ∂((volume.restrict (Ioc a b)).prod g.volumeMeasure) := by
  let W : ℝ → ℝ := fun t ↦ ∫ x, Real.exp (ξ (t, x)) * u (t, x) ^ 2 *
    g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure
  have hWc : ContinuousOn W (Icc a b) := by
    apply continuousOn_integral_of_compact_support hηc.isCompact
    · exact ((Real.continuous_exp.comp_continuousOn hξc).mul (huc.pow 2)).mul
        ((D.continuous_inner_gradient hη hη).comp continuous_snd).continuousOn
    · intro t x _ hx
      simp [D.gradient_eq_zero_of_notMem_tsupport hx]
  rw [intervalIntegral.integral_of_le hab, integral_prod _ hi, ← integral_const_mul]
  apply integral_mono_ae (hWc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hi.integral_prod_left.const_mul B)
  filter_upwards [hi.prod_right_ae] with t ht
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · filter_upwards [] with x
    apply mul_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
    by_cases hv : D.gradient η x = 0
    · simp [hv]
    · exact (g.pos x _ hv).le
  · exact ht.const_mul B
  · filter_upwards [] with x
    exact (mul_le_mul_of_nonneg_left (hgrad x) (by positivity)).trans_eq (by ring)



theorem weighted_subsolution_ae_eq_zero (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (O : M)
    {u ξ : ℝ × M → ℝ} {a b : ℝ} (hab : a ≤ b)
    {U : Set ℝ} (hU : IsOpen U) (hUab : Ioo a b ⊆ U)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (U ×ˢ univ))
    (hξ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ ξ (U ×ˢ univ))
    (huc : ContinuousOn u (Icc a b ×ˢ univ))
    (hξc : ContinuousOn ξ (Icc a b ×ˢ univ))
    (hu0 : ∀ t ∈ Ioo a b, ∀ x, 0 ≤ u (t, x))
    (hsub : ∀ t ∈ Ioo a b, ∀ x,
      deriv (fun s ↦ u (s, x)) t ≤ D.laplacian (fun y ↦ u (t, y)) x)
    (hweight : ∀ t ∈ Ioo a b, ∀ x, deriv (fun s ↦ ξ (s, x)) t +
      g.inner x (D.gradient (fun y ↦ ξ (t, y)) x)
        (D.gradient (fun y ↦ ξ (t, y)) x) ≤ 0)
    (hzero : ∀ x, u (a, x) = 0)
    (hi : Integrable (fun p : ℝ × M ↦ Real.exp (ξ p) * u p ^ 2)
      ((volume.restrict (Ioc a b)).prod g.volumeMeasure)) :
    (fun x ↦ u (b, x)) =ᵐ[g.volumeMeasure] 0 := by
  have he (j : ℕ) := D.exists_intrinsic_ball_cutoff hcomplete O
    (by linarith [Nat.cast_nonneg j (α := ℝ)] : 1 ≤ (j : ℝ) + 1)
  choose η hη hηc hηrange hηone hηsupport hηgrad using he
  let q : M → ℝ := fun x ↦ Real.exp (ξ (b, x)) * u (b, x) ^ 2
  let E : ℕ → ℝ := fun j ↦ ∫ x, η j x ^ 2 * q x ∂g.volumeMeasure
  let I : ℝ := ∫ p : ℝ × M, Real.exp (ξ p) * u p ^ 2
    ∂((volume.restrict (Ioc a b)).prod g.volumeMeasure)
  have hbc : ∀ x : M, (b, x) ∈ Icc a b ×ˢ univ :=
    fun x ↦ ⟨⟨hab, le_rfl⟩, mem_univ x⟩
  have hqc : Continuous q :=
    (Real.continuous_exp.comp (hξc.comp_continuous
      (continuous_const.prodMk continuous_id) hbc)).mul
      ((huc.comp_continuous (continuous_const.prodMk continuous_id) hbc).pow 2)
  have hq0 (x : M) : 0 ≤ q x := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hEi (j : ℕ) : Integrable (fun x ↦ η j x ^ 2 * q x) g.volumeMeasure :=
    (((hη j).continuous.pow 2).mul hqc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact (hηc j).isCompact (by
        intro x hx
        by_contra h
        exact hx (by simp [image_eq_zero_of_notMem_tsupport h])))
  have hE0 (j : ℕ) : 0 ≤ E j :=
    integral_nonneg (fun x ↦ mul_nonneg (sq_nonneg _) (hq0 x))
  have hEb (j : ℕ) : E j ≤ 4 * (heatCutoffConstant / ((j : ℝ) + 1)) ^ 2 * I := by
    have he := D.integrated_weighted_subsolution_cutoff_estimate hab hU hUab
      hu hξ huc hξc hu0 hsub hweight (hη j) (hηc j)
    have hb := D.weighted_cutoff_boundary_le hab huc hξc hi
      (hη j) (hηc j) (hηgrad j)
    simp only [mul_assoc] at hb
    simp only [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      integral_zero, zero_add, mul_assoc] at he
    change E j ≤ _ at he
    calc
      E j ≤ _ := he
      _ ≤ 4 * ((heatCutoffConstant / ((j : ℝ) + 1)) ^ 2 * I) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = _ := by ring
  have hR : Tendsto (fun j : ℕ ↦ (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun j : ℕ ↦ heatCutoffConstant / ((j : ℝ) + 1))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hR
  have hElim : Tendsto E atTop (𝓝 0) := by
    apply squeeze_zero hE0 hEb
    simpa using ((hratio.pow 2).const_mul 4).mul_const I
  have hηlim (x : M) : Tendsto (fun j : ℕ ↦ η j x ^ 2) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hR.eventually (eventually_ge_atTop (g.edist O x).toReal)] with j hj
    simp [hηone j x hj]
  have hqa := Poincare.Analysis.Heat.ae_eq_zero_of_cutoff_integral_tendsto_zero
    (Eventually.of_forall hq0) hqc.measurable.aemeasurable
    (fun j ↦ ((hη j).continuous.pow 2).measurable.aemeasurable)
    (fun j ↦ Eventually.of_forall (fun x ↦ sq_nonneg (η j x)))
    (Eventually.of_forall hηlim) hEi hElim
  filter_upwards [hqa] with x hx
  have hs : u (b, x) ^ 2 = 0 := (mul_eq_zero.mp hx).resolve_left (Real.exp_ne_zero _)
  exact (sq_eq_zero_iff).mp hs

end PoincareConjecture.LeviCivitaData
