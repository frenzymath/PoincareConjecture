import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Depth
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter

noncomputable section
set_option autoImplicit false

open Set Function
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

namespace PoincareConjecture

private theorem exists_middle_neck_profile :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧
        support φ ⊆ Icc (-(3 / 4) * ε⁻¹) ((3 / 4) * ε⁻¹) ∧
        (∀ s, |s| ≤ ε⁻¹ / 2 → φ s = 1) ∧
        ∀ s, |deriv φ s| ≤ C * ε := by
  let f : ContDiffBump (0 : ℝ) := ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩
  have hf : ContDiff ℝ ∞ (f : ℝ → ℝ) := f.contDiff
  obtain ⟨B, hB⟩ := (hf.continuous_deriv (by simp)).norm.bddAbove_range_of_hasCompactSupport
    f.hasCompactSupport.deriv.norm
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro ε hε
  let φ : ℝ → ℝ := fun s => f (ε * s)
  refine ⟨φ, hf.comp (by fun_prop), ?_, ?_, ?_⟩
  · intro s hs
    have hsf : ε * s ∈ support (f : ℝ → ℝ) := hs
    rw [f.support_eq] at hsf
    have hsmall : |ε * s| < 3 / 4 := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hsf
    rw [abs_mul, abs_of_pos hε] at hsmall
    have hsa : |s| ≤ (3 / 4) * ε⁻¹ := by
      apply (le_div_iff₀ hε).mpr
      simpa only [mul_comm] using hsmall.le
    exact ⟨by linarith [neg_abs_le s], (le_abs_self s).trans hsa⟩
  · intro s hs
    apply f.one_of_mem_closedBall
    change dist (ε * s) 0 ≤ 1 / 2
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos hε]
    have := mul_le_mul_of_nonneg_left hs hε.le
    field_simp at this
    linarith
  · intro s
    have hd : deriv φ s = deriv (f : ℝ → ℝ) (ε * s) * ε := by
      simpa only [φ, Function.comp_def, mul_one, id_eq] using
        ((hf.differentiable (by simp) _).hasDerivAt.comp s
          ((hasDerivAt_id s).const_mul ε)).deriv
    rw [hd, abs_mul, abs_of_pos hε]
    apply mul_le_mul_of_nonneg_right _ hε.le
    exact (show |deriv (f : ℝ → ℝ) (ε * s)| ≤ B from
      hB (mem_range_self _)).trans (le_max_left _ _)

namespace EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem abs_axialCutoff_sub_le_of_edist_ne_top (N : EpsilonNeck g)
    {φ : ℝ → ℝ} {a b C : ℝ}
    (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹)
    (hφ : ContDiff ℝ ∞ φ) (hs : support φ ⊆ Icc a b)
    (hC : 0 < C) (hbound : ∀ s, |deriv φ s| ≤ C)
    (x y : M) (hxy : g.edist x y ≠ ⊤) :
    |N.axialCutoff φ x - N.axialCutoff φ y| ≤
      (C / (N.scale * Real.sqrt (1 - N.epsilon))) * (g.edist x y).toReal := by
  have hfactor : 0 < N.scale * Real.sqrt (1 - N.epsilon) :=
    mul_pos N.scale_pos (Real.sqrt_pos.mpr (by linarith [N.epsilon_lt_half]))
  let K : ℝ≥0 := ⟨C / (N.scale * Real.sqrt (1 - N.epsilon)), (div_pos hC hfactor).le⟩
  have he := g.edist_le_mul_edist_of_derivative_bound
    ((N.contMDiff_axialCutoff ha hb hφ hs).of_le (by simp))
    (K := K) (div_pos hC hfactor)
    (N.abs_mvfderiv_axialCutoff_le ha hb hφ hs hC.le hbound) x y
  have hfin : (K : ℝ≥0∞) * g.edist x y ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hxy
  have hreal := ENNReal.toReal_mono hfin he
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist, Real.dist_eq,
    ENNReal.toReal_ofReal (abs_nonneg _)] at hreal
  exact hreal

end EpsilonNeck

universe u

theorem EpsilonNeck.exists_central_sphere_subset_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (N N' : EpsilonNeck g),
        N.epsilon ≤ ε₀ → N'.scale ≤ 2 * N.scale →
        N'.center ∈ N.region (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2) →
        N'.central_sphere ⊆ N.carrier := by
  obtain ⟨C, hC, hprofile⟩ := exists_middle_neck_profile
  refine ⟨min (1 / 200) (1 / (16 * Real.pi * C)), by positivity, min_le_left _ _, ?_⟩
  intro M _ _ _ _ _ _ _ g N N' hε hscale hcenter x hx
  by_contra hout
  have hNε := N.epsilon_pos
  have hNs := N.scale_pos
  have hNs' := N'.scale_pos
  have hinv := inv_pos.mpr hNε
  obtain ⟨φ, hφ, hsupp, hone, hderiv⟩ := hprofile N.epsilon hNε
  have ha : -N.epsilon⁻¹ < -(3 / 4) * N.epsilon⁻¹ := by linarith
  have hb : (3 / 4) * N.epsilon⁻¹ < N.epsilon⁻¹ := by linarith
  have hvalue : N.axialCutoff φ N'.center = 1 := by
    rw [N.axialCutoff_eq_of_mem φ hcenter.1]
    exact hone _ (abs_le.mpr ⟨by linarith [hcenter.2.1], hcenter.2.2.le⟩)
  have hzero : N.axialCutoff φ x = 0 := N.axialCutoff_eq_zero_of_not_mem φ hout
  have hdist := N'.edist_central_sphere_le_two_pi_mul_scale
    N'.center_on_central_sphere hx
  have hfinite : g.edist N'.center x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hdist
  have hdistR : (g.edist N'.center x).toReal ≤ (2 * Real.pi) * N'.scale := by
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * Real.pi) * N'.scale)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist
  have hdepth := N.abs_axialCutoff_sub_le_of_edist_ne_top ha hb hφ hsupp
    (mul_pos hC hNε) hderiv N'.center x hfinite
  rw [hvalue, hzero, sub_zero, abs_one] at hdepth
  have hroot : (1 / 2 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith [N.epsilon_lt_half])
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon), N.epsilon_lt_half]
  have hfactor : 0 < N.scale * Real.sqrt (1 - N.epsilon) := by positivity
  have hnum : N.scale * Real.sqrt (1 - N.epsilon) ≤
      C * N.epsilon * (g.edist N'.center x).toReal := by
    have := (le_div_iff₀ hfactor).mp (show 1 ≤
      (C * N.epsilon * (g.edist N'.center x).toReal) /
        (N.scale * Real.sqrt (1 - N.epsilon)) by
      simpa only [div_mul_eq_mul_div] using hdepth)
    simpa using this
  have hsmall : N.epsilon * (16 * Real.pi * C) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (hε.trans (min_le_right _ _))
  have hdistR' : (g.edist N'.center x).toReal ≤ (4 * Real.pi) * N.scale :=
    hdistR.trans (by nlinarith [mul_le_mul_of_nonneg_left hscale (show 0 ≤ 2 * Real.pi by positivity)])
  have hupper := mul_le_mul_of_nonneg_left hdistR' (mul_pos hC hNε).le
  have hquarter : C * N.epsilon * (4 * Real.pi) ≤ 1 / 4 := by nlinarith
  have hquarter' := mul_le_mul_of_nonneg_right hquarter hNs.le
  have hlower := mul_le_mul_of_nonneg_left hroot hNs.le
  nlinarith

end PoincareConjecture
