import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Heat.Dirichlet.Resolvent
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Green.ChartSupport
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Green.ChangeOfVariables
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Gradient








set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

theorem exists_chart_density_lower_bound
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKs : K ⊆ e.source) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, c ≤ g.pullbackVolumeDensity e x := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ (x) (hx : x ∈ K) := g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds (hKs hx)))
    (hD.mfderiv_injective (hKs hx))
  exact hK.exists_forall_le'
    (fun x hx => (hρ x hx).1.continuousAt.continuousWithinAt)
    (fun x hx => (hρ x hx).2)

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] [IsManifold (𝓡 n) ∞ M] in

theorem fderiv_chartPullback_apply
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source)
    (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (chartPullback e f) x v =
      mvfderiv (𝓡 n) f (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) := by
  rw [(chartPullback_eventuallyEq e f hx).fderiv_eq]
  have h := congrArg (fun L => L v) (mvfderiv_comp x
    ((hf (e x)).mdifferentiableAt (by simp))
    ((he.contMDiffAt (e.open_source.mem_nhds hx)).mdifferentiableAt (by simp)))
  simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace] at h
  convert! h using 1

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in


theorem exists_chart_fderiv_sq_bound
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKs : K ⊆ e.source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : M → ℝ), ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f →
      ∀ x ∈ K, ‖fderiv ℝ (chartPullback e f) x‖ ^ 2 ≤
        C * g.inner (e x) (D.gradient f (e x)) (D.gradient f (e x)) := by
  have hB : ContinuousOn (g.pullbackCoefficients e) K := fun x hx =>
    (g.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (e.open_source.mem_nhds (hKs hx)))).continuousAt.continuousWithinAt
  have hBn : ContinuousOn (fun x => ‖g.pullbackCoefficients e x‖) K := by
    exact (continuous_norm (E := EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).comp_continuousOn hB
  obtain ⟨A, hA⟩ := hK.bddAbove_image hBn
  let C := max A 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨C, hC, fun f hf x hx => ?_⟩
  have hBC : ‖g.pullbackCoefficients e x‖ ≤ C :=
    (hA (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hcoeff (v : EuclideanSpace ℝ (Fin n)) :
      ‖mfderiv (𝓡 n) (𝓡 n) e x v‖ ≤ Real.sqrt C * ‖v‖ := by
    have h := (g.pullbackCoefficients e x).le_opNorm₂ v v
    have hh : g.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ C * ‖v‖ ^ 2 := by
      change |g.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x v)| ≤ _ at h
      calc
        _ ≤ |g.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
            (mfderiv (𝓡 n) (𝓡 n) e x v)| := le_abs_self _
        _ ≤ ‖g.pullbackCoefficients e x‖ * ‖v‖ * ‖v‖ := h
        _ ≤ C * ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]
    change inner ℝ (mfderiv (𝓡 n) (𝓡 n) e x v)
      (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ C * ‖v‖ ^ 2 at hh
    rw [real_inner_self_eq_norm_sq] at hh
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C)
      (norm_nonneg v))).mp
    simpa only [mul_pow, Real.sq_sqrt hC] using hh
  have hop : ‖fderiv ℝ (chartPullback e f) x‖ ≤
      ‖D.gradient f (e x)‖ * Real.sqrt C := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    intro v
    rw [fderiv_chartPullback_apply e he hf (hKs hx) v, Real.norm_eq_abs]
    have h := D.abs_mvfderiv_le_gradient_norm f (e x)
      (mfderiv (𝓡 n) (𝓡 n) e x v)
    change |mvfderiv (𝓡 n) f (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)| ≤
      ‖D.gradient f (e x)‖ * ‖mfderiv (𝓡 n) (𝓡 n) e x v‖ at h
    exact h.trans (by nlinarith [hcoeff v, norm_nonneg (D.gradient f (e x))])
  change _ ≤ C * inner ℝ (D.gradient f (e x)) (D.gradient f (e x))
  rw [real_inner_self_eq_norm_sq]
  have hs := sq_le_sq₀ (norm_nonneg (fderiv ℝ (chartPullback e f) x))
    (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg C)) |>.mpr hop
  simpa only [mul_pow, Real.sq_sqrt hC, mul_comm] using hs


theorem integral_eq_chartPullback_density
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {f : M → ℝ} (hf : Continuous f) (hs : tsupport f ⊆ e.target) :
    (∫ y, f y ∂g.volumeMeasure) =
      ∫ x, chartPullback e f x * g.pullbackVolumeDensity e x := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := e.target) (fun x hx => image_eq_zero_of_notMem_tsupport
      (fun h => hx (hs h))), g.integral_target_eq_integral_pullback_density e he hei
        hf.continuousOn]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := e.source) (f := fun x => chartPullback e f x * g.pullbackVolumeDensity e x)
    (μ := volume) (fun x hx => by simp [chartPullback, indicator_of_notMem hx])]
  exact setIntegral_congr_fun e.open_source.measurableSet fun x hx => by
    rw [chartPullback_apply e f hx]

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in


theorem integrable_chartPullback_density
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ e.target) :
    Integrable (fun x => chartPullback e f x * g.pullbackVolumeDensity e x) volume := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) e.source := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds hx))
      (hD.mfderiv_injective hx)).1.continuousAt.continuousWithinAt
  have hU := (contDiff_chartPullback e he hf hc hs).continuous
  have hUs := tsupport_chartPullback_subset_source e hc hs
  have hUc := hasCompactSupport_chartPullback e hc hs
  apply Continuous.integrable_of_hasCompactSupport _ hUc.mul_right
  exact (hU.continuousOn.mul hρ).continuous_of_tsupport_subset e.open_source
    (tsupport_mul_subset_left.trans hUs)

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in
private theorem gradient_energy_nonneg (f : M → ℝ) (x : M) :
    0 ≤ g.inner x (D.gradient f x) (D.gradient f x) := by
  by_cases h : D.gradient f x = 0
  · simp [h]
  · exact (g.pos x _ h).le



theorem exists_integral_chart_fderiv_sq_le_energy
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ e.target) :
    ∃ C ≥ 0, ∀ f : EnergyTest D Ω, tsupport (f : M → ℝ) ⊆ K →
      (∫ x, ‖fderiv ℝ (chartPullback e f) x‖ ^ 2) ≤ C * ‖f‖ ^ 2 := by
  have hK' : IsCompact (e.symm '' K) :=
    hK.image_of_continuousOn (e.symm.continuousOn.mono hKs)
  have hsource : e.symm '' K ⊆ e.source := by
    rintro x ⟨y, hy, rfl⟩
    exact e.map_target (hKs hy)
  obtain ⟨c, hc, hρ⟩ := exists_chart_density_lower_bound (g := g) e he hei hK' hsource
  obtain ⟨A, hA, hder⟩ := exists_chart_fderiv_sq_bound (D := D) e he hK' hsource
  refine ⟨A / c, div_nonneg hA hc.le, fun f hf => ?_⟩
  let G : M → ℝ := fun y => g.inner y (D.gradient f y) (D.gradient f y)
  have hG := D.contMDiff_inner_gradient f.smooth f.smooth
  have hGc := D.hasCompactSupport_inner_gradient f.hasCompactSupport (f : M → ℝ)
  have hGs : tsupport G ⊆ e.target :=
    (D.tsupport_inner_gradient_subset_left f f).trans (hf.trans hKs)
  have hGi := integrable_chartPullback_density (g := g) e he hei hG hGc hGs
  have hfs := hf.trans hKs
  have hUs : tsupport (chartPullback e f) ⊆ e.symm '' K :=
    (tsupport_chartPullback_subset_image e f.hasCompactSupport hfs).trans (image_mono hf)
  have hpoint (x : EuclideanSpace ℝ (Fin n)) :
      c * ‖fderiv ℝ (chartPullback e f) x‖ ^ 2 ≤
        A * (chartPullback e G x * g.pullbackVolumeDensity e x) := by
    by_cases hx : x ∈ e.symm '' K
    · rw [chartPullback_apply e G (hsource hx)]
      have hg : 0 ≤ G (e x) := gradient_energy_nonneg f (e x)
      have hd := mul_le_mul_of_nonneg_left (hder f f.smooth x hx) hc.le
      have hr := mul_le_mul_of_nonneg_left (hρ x hx) (mul_nonneg hA hg)
      dsimp only [G] at hg ⊢
      nlinarith
    · have hd : fderiv ℝ (chartPullback e f) x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun ht => hx (hUs (tsupport_fderiv_subset ℝ ht)))
      rw [hd, norm_zero, zero_pow two_ne_zero, mul_zero]
      apply mul_nonneg hA
      apply mul_nonneg _ (Real.sqrt_nonneg _)
      by_cases hxs : x ∈ e.source
      · rw [chartPullback_apply e G hxs]
        exact gradient_energy_nonneg f (e x)
      · simp [chartPullback, indicator_of_notMem hxs]
  have hint := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x => mul_nonneg hc.le (sq_nonneg _))
    (hGi.const_mul A) (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul, integral_const_mul,
    ← integral_eq_chartPullback_density e he hei hG.continuous hGs] at hint
  have hener : (∫ y, G y ∂g.volumeMeasure) ≤ ‖f‖ ^ 2 := by
    rw [f.norm_sq, energyInner]
    exact le_add_of_nonneg_left (integral_nonneg fun y => mul_self_nonneg (f y))
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  calc
    (∫ x, ‖fderiv ℝ (chartPullback e f) x‖ ^ 2) * c ≤
        A * ∫ y, G y ∂g.volumeMeasure := by simpa only [mul_comm] using hint
    _ ≤ A * ‖f‖ ^ 2 := mul_le_mul_of_nonneg_left hener hA



theorem exists_integral_chart_sq_le_energy
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ e.target) :
    ∃ C ≥ 0, ∀ f : EnergyTest D Ω, tsupport (f : M → ℝ) ⊆ K →
      (∫ x, chartPullback e f x ^ 2) ≤ C * ‖f‖ ^ 2 := by
  have hK' : IsCompact (e.symm '' K) :=
    hK.image_of_continuousOn (e.symm.continuousOn.mono hKs)
  have hsource : e.symm '' K ⊆ e.source := by
    rintro x ⟨y, hy, rfl⟩
    exact e.map_target (hKs hy)
  obtain ⟨c, hc, hρ⟩ := exists_chart_density_lower_bound (g := g) e he hei hK' hsource
  refine ⟨c⁻¹, inv_nonneg.mpr hc.le, fun f hf => ?_⟩
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
      c * chartPullback e f x ^ 2 ≤ chartPullback e F x * g.pullbackVolumeDensity e x := by
    rw [hF]
    by_cases hx : x ∈ e.symm '' K
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hρ x hx)
        (sq_nonneg (chartPullback e f x))
    · rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hUs ht))]
      simp
  have hint := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x => mul_nonneg hc.le (sq_nonneg _))
    hFi (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul,
    ← integral_eq_chartPullback_density e he hei (f.smooth.continuous.mul
      f.smooth.continuous) hFs] at hint
  have hener : (∫ y, F y ∂g.volumeMeasure) ≤ ‖f‖ ^ 2 := by
    rw [f.norm_sq, energyInner]
    exact le_add_of_nonneg_right (integral_gradient_self_nonneg f)
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hint.trans hener)

end PoincareConjecture.LeviCivitaData.Dirichlet
