import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiDisk











set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff ComplexConjugate SchwartzMap

namespace Complex





theorem exists_annular_disk_beltrami_diffeomorphism (μ : ℂ → ℂ)
    (hμsmooth : ContDiff ℝ ∞ μ) (hzero : ∀ᶠ z in 𝓝 (0 : ℂ), μ z = 0)
    (hout : ∀ z, 1 ≤ ‖z‖ → μ z = 0) (hsub : ∀ z, ‖μ z‖ < 1) :
    ∃ f : ℂ ≃ₜ ℂ, ContDiff ℝ ∞ (f : ℂ → ℂ) ∧ ContDiff ℝ ∞ (f.symm : ℂ → ℂ) ∧
      f 0 = 0 ∧ f 1 = 1 ∧ (∀ z, ‖f z‖ ≤ 1 ↔ ‖z‖ ≤ 1) ∧
      (∀ z, ‖f z‖ < 1 ↔ ‖z‖ < 1) ∧
      ∀ z, ‖z‖ ≤ 1 → fderiv ℝ (f : ℂ → ℂ) z 1 + I * fderiv ℝ (f : ℂ → ℂ) z I =
        μ z * (fderiv ℝ (f : ℂ → ℂ) z 1 - I * fderiv ℝ (f : ℂ → ℂ) z I) := by
  have hμ0 := hzero.self_of_nhds
  have hμcompact : HasCompactSupport μ := by
    apply exists_compact_iff_hasCompactSupport.mp
    refine ⟨Metric.closedBall (0 : ℂ) 1, isCompact_closedBall _ _, ?_⟩
    intro z hz
    exact hout z (le_of_lt (lt_of_not_ge (fun h => hz (mem_closedBall_zero_iff.mpr h))))
  have hμinf : ∀ᶠ z in cocompact ℂ, μ z = 0 := by
    simpa only [coclosedCompact_eq_cocompact, Filter.EventuallyEq, Pi.zero_apply] using
      hasCompactSupport_iff_eventuallyEq.mp hμcompact
  have hJzero : ∀ᶠ z in 𝓝 (0 : ℂ), μ (beltramiCircleInversion z) = 0 := by
    have hh := beltramiCircleInversion_tendsto_infinity.eventually hμinf
    filter_upwards [eventually_nhdsWithin_iff.mp hh] with z hz
    by_cases hzne : z = 0
    · subst z
      simpa only [beltramiCircleInversion, map_zero, inv_zero] using hμ0
    · exact hz hzne
  let σ : ℂ → ℂ := fun z => (z / conj z) ^ 2
  let ν : ℂ → ℂ := fun z => μ z + σ z * conj (μ (beltramiCircleInversion z))
  have hνzero : ∀ᶠ z in 𝓝 (0 : ℂ), ν z = 0 := by
    filter_upwards [hzero, hJzero] with z hz hj
    simp only [ν, hz, hj, map_zero, mul_zero, add_zero]
  have hνsmooth : ContDiff ℝ ∞ ν := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z = 0
    · subst z
      exact contDiffAt_const.congr_of_eventuallyEq hνzero
    · have hσ : ContDiffAt ℝ ∞ σ z := by
        simpa only [σ, div_eq_mul_inv] using!
          ((contDiffAt_id : ContDiffAt ℝ ∞ (fun z : ℂ => z) z).mul
            (conjCLE.contDiff.contDiffAt.inv (star_ne_zero.mpr hz))).pow 2
      have hμJ := hμsmooth.contDiffAt.comp z (contDiffAt_beltramiCircleInversion hz)
      exact hμsmooth.contDiffAt.add (hσ.mul (conjCLE.contDiff.contDiffAt.comp z hμJ))
  have hνcompact : HasCompactSupport ν := by
    rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact]
    filter_upwards [hμinf,
      (beltramiCircleInversion_tendsto_zero.mono_right nhdsWithin_le_nhds).eventually hzero]
      with z hz hj
    simp only [ν, hz, hj, map_zero, mul_zero, add_zero, Pi.zero_apply]
  have hinside (z : ℂ) (hz : ‖z‖ ≤ 1) : ν z = μ z := by
    have hj : μ (beltramiCircleInversion z) = 0 := by
      by_cases hne : z = 0
      · subst z
        simpa only [beltramiCircleInversion, map_zero, inv_zero] using hμ0
      · apply hout
        simp only [beltramiCircleInversion, norm_inv, norm_conj]
        exact (one_le_inv₀ (norm_pos_iff.mpr hne)).mpr hz
    simp only [ν, hj, map_zero, mul_zero, add_zero]
  obtain ⟨zmax, hmax⟩ :=
    hμsmooth.continuous.norm.exists_forall_ge_of_hasCompactSupport hμcompact.norm
  have hνbound (z : ℂ) : ‖ν z‖ ≤ ‖μ zmax‖ := by
    by_cases hz : ‖z‖ ≤ 1
    · rw [hinside z hz]
      exact hmax z
    · have hzne : z ≠ 0 := by intro he; simp only [he, norm_zero] at hz; exact hz (by norm_num)
      have hσ : ‖σ z‖ = 1 := by
        simp only [σ, norm_pow, norm_div, norm_conj,
          div_self (norm_ne_zero_iff.mpr hzne), one_pow]
      simp only [ν, hout z (le_of_lt (lt_of_not_ge hz)), zero_add, norm_mul, norm_conj, hσ, one_mul]
      exact hmax _
  have href (z : ℂ) (hz : z ≠ 0) :
      ν z = (z / conj z) ^ 2 * conj (ν (beltramiCircleInversion z)) := by
    have hc : conj z ≠ 0 := star_ne_zero.mpr hz
    dsimp only [ν, σ]
    simp only [map_add, map_mul, map_pow, map_div₀, conj_conj,
      beltramiCircleInversion, map_inv₀]
    field_simp
    ring
  let νS := hνcompact.toSchwartzMap hνsmooth
  obtain ⟨f, hf, hfi, hf0, hf1, hclosed, hopen, heq⟩ :=
    exists_disk_smooth_beltrami_diffeomorphism νS hνcompact (hsub zmax) hνbound hνzero href
  refine ⟨f, hf, hfi, hf0, hf1, hclosed, hopen, ?_⟩
  intro z hz
  have hh := heq z
  change _ = ν z * _ at hh
  rw [hinside z hz] at hh
  exact hh

end Complex
