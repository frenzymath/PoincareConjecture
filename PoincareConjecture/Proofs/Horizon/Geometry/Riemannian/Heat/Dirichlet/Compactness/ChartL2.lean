import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Resolvent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.ChartSupport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.ChangeOfVariables

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

theorem integral_sq_eq_chartPullback_density
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {f : M → ℝ} (hf : Continuous f) (hs : tsupport f ⊆ e.target) :
    (∫ x, f x ^ 2 ∂g.volumeMeasure) =
      ∫ x, chartPullback e f x ^ 2 * g.pullbackVolumeDensity e x := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := e.target) (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), zero_pow two_ne_zero])]
  rw [g.integral_target_eq_integral_pullback_density e he hei
    (f := fun x => f x ^ 2) (hf.pow 2).continuousOn]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := e.source) (f := fun x => chartPullback e f x ^ 2 * g.pullbackVolumeDensity e x)
    (μ := volume) (fun x hx => by simp [chartPullback, indicator_of_notMem hx])]
  exact setIntegral_congr_fun e.open_source.measurableSet fun x hx => by
    rw [chartPullback_apply e f hx]

theorem exists_integral_sq_le_chartPullback
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ e.target) :
    ∃ C ≥ 0, ∀ f : EnergyTest D Ω, tsupport (f : M → ℝ) ⊆ K →
      (∫ x, f x ^ 2 ∂g.volumeMeasure) ≤ C * ∫ x, chartPullback e f x ^ 2 := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hK' : IsCompact (e.symm '' K) :=
    hK.image_of_continuousOn (e.symm.continuousOn.mono hKs)
  have hsource : e.symm '' K ⊆ e.source := by
    rintro x ⟨y, hy, rfl⟩
    exact e.map_target (hKs hy)
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) (e.symm '' K) := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds (hsource hx)))
      (hD.mfderiv_injective (hsource hx))).1.continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hK'.exists_bound_of_continuousOn hρ
  refine ⟨|C|, abs_nonneg C, fun f hf => ?_⟩
  have hfs := hf.trans hKs
  have hU := contDiff_chartPullback e he f.smooth f.hasCompactSupport hfs
  have hUc := hasCompactSupport_chartPullback e f.hasCompactSupport hfs
  have hUs : tsupport (chartPullback e f) ⊆ e.symm '' K :=
    (tsupport_chartPullback_subset_image e f.hasCompactSupport hfs).trans (image_mono hf)
  have hUi : Integrable (fun x => chartPullback e f x ^ 2) volume := by
    convert!
      (hU.continuous.mul hU.continuous).integrable_of_hasCompactSupport
        (μ := volume) (hUc.mul_right (f := chartPullback e f)) using 1
    funext x
    exact pow_two _
  rw [integral_sq_eq_chartPullback_density e he hei f.smooth.continuous hfs,
    ← integral_const_mul]
  apply integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _)
      (Real.sqrt_nonneg _))
    (hUi.const_mul |C|)
  apply Filter.Eventually.of_forall
  intro x
  change chartPullback e f x ^ 2 * g.pullbackVolumeDensity e x ≤
    |C| * chartPullback e f x ^ 2
  by_cases hx : x ∈ e.symm '' K
  · have hbound : g.pullbackVolumeDensity e x ≤ |C| :=
      (le_abs_self _).trans ((hC x hx).trans (le_abs_self C))
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbound
      (sq_nonneg (chartPullback e f x))
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hUs h))]
    simp

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

theorem EnergyTest.chartPullback_memLp
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (f : EnergyTest D Ω) (hs : tsupport (f : M → ℝ) ⊆ e.target) :
    MemLp (chartPullback e f) 2 volume :=
  (contDiff_chartPullback e he f.smooth f.hasCompactSupport hs).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_chartPullback e f.hasCompactSupport hs)

def EnergyTest.chartToL2
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (f : EnergyTest D Ω) (hs : tsupport (f : M → ℝ) ⊆ e.target) : Lp ℝ 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (f.chartPullback_memLp e he hs).toLp _

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

theorem EnergyTest.norm_chartToL2_sq
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (f : EnergyTest D Ω) (hs : tsupport (f : M → ℝ) ⊆ e.target) :
    ‖f.chartToL2 e he hs‖ ^ 2 = ∫ x, chartPullback e f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(f.chartPullback_memLp e he hs).coeFn_toLp] with x hx
  change inner ℝ (f.chartToL2 e he hs x) (f.chartToL2 e he hs x) = _
  change inner ℝ ((f.chartPullback_memLp e he hs).toLp _ x)
    ((f.chartPullback_memLp e he hs).toLp _ x) = _
  rw [hx]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem exists_norm_testToL2_le_chartToL2
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ e.target) :
    ∃ C ≥ 0, ∀ (f : EnergyTest D Ω) (hf : tsupport (f : M → ℝ) ⊆ K),
      ‖testToL2 D Ω f‖ ≤ C * ‖f.chartToL2 e he (hf.trans hKs)‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_integral_sq_le_chartPullback
    (D := D) (Ω := Ω) e he hei hK hKs
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, fun f hf => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hC, f.norm_chartToL2_sq,
    ← real_inner_self_eq_norm_sq, testToL2_inner]
  simpa only [pow_two] using hbound f hf

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in
@[simp] theorem EnergyTest.coe_sub (f h : EnergyTest D Ω) :
    ⇑(f - h) = fun x => f x - h x := rfl

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

theorem EnergyTest.chartToL2_sub
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (f h : EnergyTest D Ω) (hf : tsupport (f : M → ℝ) ⊆ e.target)
    (hh : tsupport (h : M → ℝ) ⊆ e.target) :
    (f - h).chartToL2 e he ((tsupport_sub f h).trans (union_subset hf hh)) =
      f.chartToL2 e he hf - h.chartToL2 e he hh := by
  have hsub : chartPullback e (f - h) = chartPullback e f - chartPullback e h := by
    funext x
    by_cases hx : x ∈ e.source
    · simp only [chartPullback_apply e _ hx, Pi.sub_apply]
    · simp [chartPullback, indicator_of_notMem hx]
  exact ((f - h).chartPullback_memLp e he
    ((tsupport_sub f h).trans (union_subset hf hh))).toLp_congr
    ((f.chartPullback_memLp e he hf).sub (h.chartPullback_memLp e he hh))
    (Filter.Eventually.of_forall fun x => congrFun hsub x) |>.trans
      ((f.chartPullback_memLp e he hf).toLp_sub (h.chartPullback_memLp e he hh))

theorem cauchySeq_testToL2_of_chartToL2
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ e.target)
    (f : ℕ → EnergyTest D Ω) (hf : ∀ k, tsupport (f k : M → ℝ) ⊆ K)
    (hc : CauchySeq (fun k => (f k).chartToL2 e he ((hf k).trans hKs))) :
    CauchySeq (fun k => testToL2 D Ω (f k)) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_testToL2_le_chartToL2
    (D := D) (Ω := Ω) e he hei hK hKs
  refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (ε / (C + 1)) (div_pos hε (by positivity))
  refine ⟨N, fun i hi j hj => ?_⟩
  have hij := hbound (f i - f j) ((tsupport_sub _ _).trans (union_subset (hf i) (hf j)))
  rw [EnergyTest.chartToL2_sub e he (f i) (f j) ((hf i).trans hKs) ((hf j).trans hKs),
    map_sub, ← dist_eq_norm, ← dist_eq_norm] at hij
  refine hij.trans_lt ?_
  have hd := hN i hi j hj
  have hd0 := dist_nonneg (x := (f i).chartToL2 e he ((hf i).trans hKs))
    (y := (f j).chartToL2 e he ((hf j).trans hKs))
  have hpos : 0 < C + 1 := by positivity
  have := (lt_div_iff₀ hpos).mp hd
  nlinarith

end PoincareConjecture.LeviCivitaData.Dirichlet
