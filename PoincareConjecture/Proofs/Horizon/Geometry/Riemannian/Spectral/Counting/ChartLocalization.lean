import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Compactness.ChartEnergy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Compactness.ChartL2
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Compactness.Localization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Density

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet.Counting

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

theorem exists_norm_chartToL2_le_testToL2
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ e.target) :
    ∃ C ≥ 0, ∀ (f : EnergyTest D Ω) (hf : tsupport (f : M → ℝ) ⊆ K),
      ‖f.chartToL2 e he (hf.trans hKs)‖ ≤ C * ‖testToL2 D Ω f‖ := by
  have hK' : IsCompact (e.symm '' K) :=
    hK.image_of_continuousOn (e.symm.continuousOn.mono hKs)
  have hsource : e.symm '' K ⊆ e.source := by
    rintro x ⟨y, hy, rfl⟩
    exact e.map_target (hKs hy)
  obtain ⟨c, hc, hρ⟩ := exists_chart_density_lower_bound (g := g) e he hei hK' hsource
  refine ⟨Real.sqrt c⁻¹, Real.sqrt_nonneg _, fun f hf => ?_⟩
  have hfs := hf.trans hKs
  have hUs : tsupport (chartPullback e f) ⊆ e.symm '' K :=
    (tsupport_chartPullback_subset_image e f.hasCompactSupport hfs).trans (image_mono hf)
  let F : M → ℝ := fun y => f y * f y
  have hFs : tsupport F ⊆ e.target := tsupport_mul_subset_left.trans hfs
  have hFi := integrable_chartPullback_density (g := g) e he hei
    (f.smooth.mul f.smooth) f.hasCompactSupport.mul_right hFs
  have hF (x : EuclideanSpace ℝ (Fin n)) :
      chartPullback e F x = chartPullback e f x ^ 2 := by
    by_cases hx : x ∈ e.source
    · simp only [chartPullback_apply e _ hx, F, pow_two]
    · simp [chartPullback, indicator_of_notMem hx]
  have hpoint (x : EuclideanSpace ℝ (Fin n)) :
      c * chartPullback e f x ^ 2 ≤
        chartPullback e F x * g.pullbackVolumeDensity e x := by
    rw [hF]
    by_cases hx : x ∈ e.symm '' K
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hρ x hx)
        (sq_nonneg (chartPullback e f x))
    · rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hUs ht))]
      simp
  have hint := integral_mono_of_nonneg
    (Eventually.of_forall fun x => mul_nonneg hc.le (sq_nonneg _))
    hFi (Eventually.of_forall hpoint)
  rw [integral_const_mul,
    ← integral_eq_chartPullback_density e he hei (f.smooth.continuous.mul
      f.smooth.continuous) hFs] at hint
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr hc.le), f.norm_chartToL2_sq,
    ← real_inner_self_eq_norm_sq, testToL2_inner, inv_mul_eq_div]
  exact (le_div_iff₀ hc).mpr (by simpa only [Pi.mul_apply, mul_comm] using hint)

theorem exists_norm_testToL2_mulSmooth_le (χ : M → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) (hc : HasCompactSupport χ) :
    ∃ C ≥ 0, ∀ f : EnergyTest D Ω,
      ‖testToL2 D Ω (f.mulSmooth χ hχ)‖ ≤ C * ‖testToL2 D Ω f‖ := by
  obtain ⟨a, ha⟩ := (hc.mul_right (f := χ)).exists_bound_of_continuous
    (hχ.continuous.mul hχ.continuous)
  have ha' (x : M) : χ x ^ 2 ≤ |a| := by
    have := (le_abs_self (χ x * χ x)).trans ((ha x).trans (le_abs_self a))
    simpa only [pow_two] using this
  refine ⟨Real.sqrt |a|, Real.sqrt_nonneg _, fun f => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (abs_nonneg _),
    ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    testToL2_inner, testToL2_inner, ← integral_const_mul]
  apply integral_mono ((f.mulSmooth χ hχ).integrable_mul _)
    ((f.integrable_mul f).const_mul |a|)
  intro x
  have hb := mul_le_mul_of_nonneg_right (ha' x) (sq_nonneg (f x))
  simpa only [EnergyTest.mulSmooth_apply, pow_two, mul_assoc, mul_left_comm,
    mul_comm] using hb

def testToDomainL2 (D : LeviCivitaData g) (Ω : Set M) :
    EnergyTest D Ω →ₗ[ℝ] Lp ℝ 2 (g.volumeMeasure.restrict Ω) :=
  ((toDomainL2 D Ω).comp Completion.toComplL).toLinearMap

@[simp] theorem testToDomainL2_apply (f : EnergyTest D Ω) :
    testToDomainL2 D Ω f = toDomainL2 D Ω (f : H1Zero D Ω) := rfl

theorem norm_testToDomainL2 (hΩ : MeasurableSet Ω) (f : EnergyTest D Ω) :
    ‖testToDomainL2 D Ω f‖ = ‖testToL2 D Ω f‖ := by
  rw [testToDomainL2_apply, norm_toDomainL2 hΩ, toL2_coe]

theorem denseRange_testToDomainL2 (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω)) :
    DenseRange (testToDomainL2 D Ω) :=
  (denseRange_toDomainL2 hΩ hc).comp Completion.denseRange_coe
    (toDomainL2 D Ω).continuous

def chartLocalizationTest (D : LeviCivitaData g) (Ω : Set M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hs : tsupport χ ⊆ e.target) :
    EnergyTest D Ω →ₗ[ℝ] Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) where
  toFun f := (f.mulSmooth χ hχ).chartToL2 e he
    ((f.mulSmooth_support_subset χ hχ).trans hs)
  map_add' f h := by
    let hf := (f.mulSmooth χ hχ).chartPullback_memLp e he
      ((f.mulSmooth_support_subset χ hχ).trans hs)
    let hh := (h.mulSmooth χ hχ).chartPullback_memLp e he
      ((h.mulSmooth_support_subset χ hχ).trans hs)
    apply (MemLp.toLp_congr _ (hf.add hh) (Eventually.of_forall ?_)).trans
      (hf.toLp_add hh)
    intro x
    by_cases hx : x ∈ e.source
    · simp [chartPullback_apply e _ hx, mul_add]
    · simp [chartPullback, indicator_of_notMem hx]
  map_smul' c f := by
    let hf := (f.mulSmooth χ hχ).chartPullback_memLp e he
      ((f.mulSmooth_support_subset χ hχ).trans hs)
    apply (MemLp.toLp_congr _ (hf.const_smul c) (Eventually.of_forall ?_)).trans
      (hf.toLp_const_smul c)
    intro x
    by_cases hx : x ∈ e.source
    · simp [chartPullback_apply e _ hx, mul_left_comm]
    · simp [chartPullback, indicator_of_notMem hx]

theorem exists_norm_chartLocalizationTest_le
    (hΩ : MeasurableSet Ω)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ e.target) :
    ∃ C ≥ 0, ∀ f : EnergyTest D Ω,
      ‖chartLocalizationTest D Ω e he χ hχ hs f‖ ≤ C * ‖testToDomainL2 D Ω f‖ := by
  obtain ⟨A, hA, hchart⟩ := exists_norm_chartToL2_le_testToL2
    (D := D) (Ω := Ω) e he hei hc hs
  obtain ⟨B, hB, hmul⟩ := exists_norm_testToL2_mulSmooth_le (D := D) (Ω := Ω) χ hχ hc
  refine ⟨A * B, mul_nonneg hA hB, fun f => ?_⟩
  rw [norm_testToDomainL2 hΩ, mul_assoc]
  exact (hchart (f.mulSmooth χ hχ) (f.mulSmooth_support_subset χ hχ)).trans
    (mul_le_mul_of_nonneg_left (hmul f) hA)

def chartLocalization (D : LeviCivitaData g) (Ω : Set M)
    (_hΩ : IsOpen Ω) (_hcΩ : IsCompact (closure Ω))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (_hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (_hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ e.target) :
    Lp ℝ 2 (g.volumeMeasure.restrict Ω) →L[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (chartLocalizationTest D Ω e he χ hχ hsχ).extendOfNorm (testToDomainL2 D Ω)

@[simp] theorem chartLocalization_test (hΩ : IsOpen Ω) (hcΩ : IsCompact (closure Ω))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ e.target)
    (f : EnergyTest D Ω) :
    chartLocalization D Ω hΩ hcΩ e he hei χ hχ hcχ hsχ
        (toDomainL2 D Ω (f : H1Zero D Ω)) =
      (f.mulSmooth χ hχ).chartToL2 e he ((f.mulSmooth_support_subset χ hχ).trans hsχ) := by
  obtain ⟨C, _, hC⟩ := exists_norm_chartLocalizationTest_le
    (D := D) (Ω := Ω) hΩ.measurableSet e he hei χ hχ hcχ hsχ
  exact LinearMap.extendOfNorm_eq (denseRange_testToDomainL2 hΩ hcΩ) ⟨C, hC⟩ f

end PoincareConjecture.LeviCivitaData.Dirichlet.Counting
