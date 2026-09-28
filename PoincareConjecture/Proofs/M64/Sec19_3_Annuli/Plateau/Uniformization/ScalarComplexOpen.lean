import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationCompactification
import Mathlib.Analysis.Complex.OpenMapping













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter ComplexConjugate
open scoped Topology ContDiff

namespace PoincareConjecture.M64Uniformization

private theorem conformal_directions (L : ℂ →L[ℝ] ℂ) (h : IsConformalMap L) :
    L Complex.I = Complex.I * L 1 ∨ L Complex.I = -Complex.I * L 1 := by
  rcases h.is_complex_or_conj_linear with ⟨K, hK⟩ | ⟨K, hK⟩
  · left
    rw [← hK]
    simpa only [ContinuousLinearMap.coe_restrictScalars', smul_eq_mul, mul_one]
      using K.map_smul Complex.I (1 : ℂ)
  · right
    have h1 : K 1 = L 1 := by
      simpa using congrArg (fun T : ℂ →L[ℝ] ℂ => T 1) hK
    have hi : K Complex.I = -L Complex.I := by
      simpa using congrArg (fun T : ℂ →L[ℝ] ℂ => T Complex.I) hK
    have hm : K Complex.I = Complex.I * K 1 := by
      simpa only [smul_eq_mul, mul_one] using K.map_smul Complex.I (1 : ℂ)
    rw [h1, hi] at hm
    linear_combination -hm

private theorem conformal_orientation {f : ℂ → ℂ} {S : Set ℂ}
    (hS : IsOpen S) (hSc : IsPreconnected S) (hf : ContDiffOn ℝ ∞ f S)
    (hc : ∀ z ∈ S, IsConformalMap (fderiv ℝ f z)) :
    (∀ z ∈ S, DifferentiableAt ℂ f z) ∨
      (∀ z ∈ S, DifferentiableAt ℂ (conj ∘ f) z) := by
  let L := fderiv ℝ f
  let sigma : ℂ → ℝ := fun z => (L z Complex.I / L z 1).im
  have hn (z : ℂ) (hz : z ∈ S) : L z 1 ≠ 0 := by
    simpa only [map_zero] using (hc z hz).injective.ne (one_ne_zero : (1 : ℂ) ≠ 0)
  have hd (z : ℂ) (hz : z ∈ S) : DifferentiableAt ℝ f z :=
    (hf.contDiffAt (hS.mem_nhds hz)).differentiableAt (by simp)
  have hLc : ContinuousOn L S := hf.continuousOn_fderiv_of_isOpen hS (by simp)
  have hsig : ContinuousOn sigma S := Complex.continuous_im.comp_continuousOn
    ((hLc.clm_apply continuousOn_const).div (hLc.clm_apply continuousOn_const) hn)
  have hside (z : ℂ) (hz : z ∈ S) :
      (sigma z = 1 ∧ L z Complex.I = Complex.I * L z 1) ∨
        (sigma z = -1 ∧ L z Complex.I = -Complex.I * L z 1) := by
    rcases conformal_directions (L z) (hc z hz) with hh | hh
    · exact Or.inl ⟨by dsimp [sigma]; rw [hh, mul_div_cancel_right₀ _ (hn z hz)]; rfl, hh⟩
    · exact Or.inr ⟨by dsimp [sigma]; rw [hh, mul_div_cancel_right₀ _ (hn z hz)]; rfl, hh⟩
  have hsne (z : ℂ) (hz : z ∈ S) : sigma z ≠ 0 := by
    rcases hside z hz with hh | hh <;> rw [hh.1] <;> norm_num
  rcases hSc.mapsTo_Ioi_or_Iio hsig hsne with hpos | hneg
  · left
    intro z hz
    have he : L z Complex.I = Complex.I * L z 1 := by
      rcases hside z hz with hh | hh
      · exact hh.2
      · have h := hpos hz
        rw [mem_Ioi, hh.1] at h
        norm_num at h
    exact differentiableAt_complex_iff_differentiableAt_real.mpr
      ⟨hd z hz, by simpa only [smul_eq_mul] using he⟩
  · right
    intro z hz
    have he : L z Complex.I = -Complex.I * L z 1 := by
      rcases hside z hz with hh | hh
      · have h := hneg hz
        rw [mem_Iio, hh.1] at h
        norm_num at h
      · exact hh.2
    have hder := Complex.conjCLE.hasFDerivAt.comp z (hd z hz).hasFDerivAt
    apply differentiableAt_complex_iff_differentiableAt_real.mpr
    refine ⟨hder.differentiableAt, ?_⟩
    change fderiv ℝ (Complex.conjCLE ∘ f) z Complex.I =
      Complex.I • fderiv ℝ (Complex.conjCLE ∘ f) z 1
    rw [hder.fderiv]
    change conj (L z Complex.I) = Complex.I * conj (L z 1)
    rw [he]
    simp

private theorem punctured_ball_preconnected (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsPreconnected (Metric.ball c r \ {c}) := by
  let e := OpenPartialHomeomorph.univBall c r
  have he : Function.Injective e := (e.isOpenEmbedding (by simp [e])).injective
  have himg : e '' ({0}ᶜ : Set ℂ) = Metric.ball c r \ {c} := by
    rw [compl_eq_univ_sdiff, image_sdiff he]
    have hu : e '' univ = Metric.ball c r := by
      simpa [e, OpenPartialHomeomorph.univBall_target c hr] using e.image_source_eq_target
    rw [hu, image_singleton]
    simp [e]
  rw [← himg]
  apply (isPathConnected_compl_singleton_of_one_lt_rank
    (by rw [← Module.finrank_eq_rank]; norm_num) (0 : ℂ)).isConnected.isPreconnected.image
  exact (OpenPartialHomeomorph.continuous_univBall c r).continuousOn





theorem scalar_analytic_or_conjugate_of_conformal_punctured {f : ℂ → ℂ} {c : ℂ}
    (hc : ContinuousAt f c)
    (hf : ∀ᶠ z in 𝓝[≠] c, ContDiffAt ℝ ∞ f z ∧ IsConformalMap (fderiv ℝ f z)) :
    AnalyticAt ℂ f c ∨ AnalyticAt ℂ (conj ∘ f) c := by
  obtain ⟨r, hr, hball⟩ := (nhdsWithin_hasBasis Metric.nhds_basis_ball _).mem_iff.mp hf
  have hS : IsOpen (Metric.ball c r \ {c}) := Metric.isOpen_ball.sdiff isClosed_singleton
  have hs : ContDiffOn ℝ ∞ f (Metric.ball c r \ {c}) :=
    fun z hz => (hball hz).1.contDiffWithinAt
  have hmem : Metric.ball c r \ {c} ∈ 𝓝[≠] c :=
    inter_mem (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds c hr)) self_mem_nhdsWithin
  rcases conformal_orientation hS (punctured_ball_preconnected c hr)
      hs (fun z hz => (hball hz).2) with h | h
  · exact Or.inl (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (Filter.Eventually.mono hmem h) hc)
  · exact Or.inr (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (Filter.Eventually.mono hmem h)
      (Complex.continuous_conj.continuousAt.comp hc))





theorem scalar_nhds_le_map_of_conformal_punctured {f : ℂ → ℂ} {c : ℂ}
    (hc : ContinuousAt f c)
    (hf : ∀ᶠ z in 𝓝[≠] c, ContDiffAt ℝ ∞ f z ∧ IsConformalMap (fderiv ℝ f z)) :
    𝓝 (f c) ≤ map f (𝓝 c) := by
  have hnot : ¬ ∀ᶠ z in 𝓝 c, f z = f c := by
    intro heq
    have hzero : ∀ᶠ z in 𝓝 c, fderiv ℝ f z = 0 := by
      filter_upwards [heq.eventually_nhds] with z hz
      have hz' : f =ᶠ[𝓝 z] fun _ => f c := hz
      exact hz'.fderiv_eq.trans (by simp)
    obtain ⟨z, hz, hconf⟩ := ((hzero.filter_mono nhdsWithin_le_nhds).and hf).exists
    have hinj := hconf.2.injective
    rw [hz] at hinj
    have h01 : (0 : ℂ) = 1 := hinj rfl
    exact zero_ne_one h01
  rcases scalar_analytic_or_conjugate_of_conformal_punctured hc hf with ha | ha
  · exact ha.eventually_constant_or_nhds_le_map_nhds.resolve_left hnot
  · have hnotc : ¬ ∀ᶠ z in 𝓝 c, conj (f z) = conj (f c) := by
      intro heq
      exact hnot (heq.mono fun z hz => Complex.conjCLE.injective hz)
    have hopen := ha.eventually_constant_or_nhds_le_map_nhds.resolve_left hnotc
    have hmap := Filter.map_mono (m := conj) hopen
    have hnhds : map conj (𝓝 (conj (f c))) = 𝓝 (f c) := by
      have h := Complex.conjCLE.toHomeomorph.map_nhds_eq (conj (f c))
      change map conj (𝓝 (conj (f c))) = 𝓝 (conj (conj (f c))) at h
      simpa only [Complex.conj_conj] using h
    change map conj (𝓝 (conj (f c))) ≤ _ at hmap
    rw [hnhds] at hmap
    simpa only [map_map, Function.comp_def, Complex.conj_conj] using hmap





theorem scalar_fiber_isolated_of_conformal_punctured {f : ℂ → ℂ} {c : ℂ}
    (hc : ContinuousAt f c)
    (hf : ∀ᶠ z in 𝓝[≠] c, ContDiffAt ℝ ∞ f z ∧ IsConformalMap (fderiv ℝ f z)) :
    ∀ᶠ z in 𝓝[≠] c, f z ≠ f c := by
  have hnot : ¬ ∀ᶠ z in 𝓝 c, f z = f c := by
    intro heq
    have hzero : ∀ᶠ z in 𝓝 c, fderiv ℝ f z = 0 := by
      filter_upwards [heq.eventually_nhds] with z hz
      have hz' : f =ᶠ[𝓝 z] fun _ => f c := hz
      exact hz'.fderiv_eq.trans (by simp)
    obtain ⟨z, hz, hconf⟩ := ((hzero.filter_mono nhdsWithin_le_nhds).and hf).exists
    have hinj := hconf.2.injective
    rw [hz] at hinj
    have h01 : (0 : ℂ) = 1 := hinj rfl
    exact zero_ne_one h01
  rcases scalar_analytic_or_conjugate_of_conformal_punctured hc hf with ha | ha
  · exact (ha.eventually_eq_or_eventually_ne analyticAt_const).resolve_left hnot
  · have hnotc : ¬ ∀ᶠ z in 𝓝 c, conj (f z) = conj (f c) := by
      intro heq
      exact hnot (heq.mono fun z hz => Complex.conjCLE.injective hz)
    have hi := (ha.eventually_eq_or_eventually_ne analyticAt_const).resolve_left hnotc
    exact hi.mono fun z hz heq => hz (congrArg conj heq)

end PoincareConjecture.M64Uniformization
