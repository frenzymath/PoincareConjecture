import PoincareConjecture.Proofs.M60.Mathlib.ChartApproximation
import PoincareConjecture.Proofs.M40.Mathlib.SupportedChartSmoothing










set_option autoImplicit false

open Set Function Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M60

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [MetricSpace N] [ChartedSpace F N]





theorem exists_homotopic_chart_smoothing
    (e : OpenPartialHomeomorph M E) (h : OpenPartialHomeomorph N F)
    (he : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e e.source)
    (hh : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ h h.source)
    (hh' : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ h.symm h.target)
    (rho : M → ℝ) (hrho : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ rho)
    (hrho01 : ∀ x, rho x ∈ Icc 0 1) (hK : IsCompact (tsupport rho))
    (hKe : tsupport rho ⊆ e.source)
    (f : C(M, N)) (hfK : MapsTo f (tsupport rho) h.source)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ g : C(M, N),
      (∀ x, rho =ᶠ[𝓝 x] 1 → ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g x) ∧
      (∀ x, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x →
        ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g x) ∧
      g.Homotopic f ∧ ∀ x, dist (g x) (f x) < epsilon := by
  let U := e.source ∩ f ⁻¹' h.source
  have hU : IsOpen U := e.open_source.inter (h.open_source.preimage f.continuous)
  have hUe : U ⊆ e.source := inter_subset_left
  have hsupport : tsupport rho ⊆ U := fun x hx => ⟨hKe hx, hfK hx⟩
  have hfU : MapsTo f U h.source := fun _ hx => hx.2
  have hcoord : ContinuousOn (fun z => h (f (e.symm z))) (e '' tsupport rho) := by
    rintro z ⟨x, hx, rfl⟩
    have hfx : f (e.symm (e x)) ∈ h.source := by rw [e.left_inv (hKe hx)]; exact hfK hx
    exact ((h.continuousAt hfx).comp (f := fun z => f (e.symm z))
      (f.continuous.continuousAt.comp (f := e.symm)
        (e.continuousAt_symm (e.map_source (hKe hx))))).continuousWithinAt
  have hsourceImage : IsCompact (e '' tsupport rho) :=
    hK.image_of_continuousOn (e.continuousOn.mono hKe)
  have htargetImage : IsCompact ((h ∘ f) '' tsupport rho) :=
    hK.image_of_continuousOn (h.continuousOn.comp f.continuous.continuousOn hfK)
  obtain ⟨delta, hdelta, hcontrol⟩ := exists_pos_inverse_chart_control h htargetImage
    (by rintro _ ⟨x, hx, rfl⟩; exact h.map_source (hfK hx)) hepsilon
  obtain ⟨G, hG, hGclose⟩ := exists_contDiff_approx_on_isClosed
    hsourceImage.isClosed hcoord hdelta
  have hGclose' (x : M) (hx : x ∈ tsupport rho) :
      dist (G (e x)) (h (f x)) < delta := by
    simpa only [e.left_inv (hKe hx)] using hGclose (e x) (mem_image_of_mem e hx)
  let displacement := M40.chartSmoothingDisplacement e h rho f G
  have hcontrol' (t : unitInterval) (x : M) (hx : x ∈ tsupport rho) :
      h (f x) + (t : ℝ) • displacement x ∈ h.target ∧
      dist (h.symm (h (f x) + (t : ℝ) • displacement x)) (f x) < epsilon := by
    have ht : (t : ℝ) * rho x ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg t.property.1 (hrho01 x).1,
        (mul_le_mul_of_nonneg_right t.property.2 (hrho01 x).1).trans
          (by simpa using (hrho01 x).2)⟩
    have hclose : dist (h (f x) + (t : ℝ) • displacement x) (h (f x)) < delta := by
      have hq : h (f x) + (t : ℝ) • displacement x - h (f x) =
          ((t : ℝ) * rho x) • (G (e x) - h (f x)) := by
        dsimp [displacement, M40.chartSmoothingDisplacement]
        module
      rw [dist_eq_norm, hq, norm_smul, Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt
        (by simpa only [dist_eq_norm] using hGclose' x hx)
    have hc := hcontrol (h (f x)) (mem_image_of_mem (h ∘ f) hx) _ hclose
    rwa [h.left_inv (hfK hx)] at hc
  have hrange (t : unitInterval) (x : M) (hx : x ∈ U) :
      h (f x) + (t : ℝ) • displacement x ∈ h.target := by
    by_cases hxs : x ∈ tsupport rho
    · exact (hcontrol' t x hxs).1
    · have hr0 := image_eq_zero_of_notMem_tsupport hxs
      simpa only [displacement, M40.chartSmoothingDisplacement, hr0,
        zero_smul, smul_zero, add_zero] using h.map_source (hfU hx)
  have hrange1 (x : M) (hx : x ∈ U) : h (f x) + displacement x ∈ h.target := by
    simpa using hrange 1 x hx
  let g := M40.supportedChartSmoothing e h U rho f G
  have hg : Continuous g := M40.continuous_supportedChartSmoothing e h hU hUe
    hrho.continuous f.continuous hG.continuous hsupport hfU hrange1
  refine ⟨⟨g, hg⟩, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact M40.contMDiffAt_supportedChartSmoothing_of_eventuallyEq_one e h hU hUe hG
      he hh' hsupport hrange1 hx
  · intro x hx
    exact M40.contMDiffAt_supportedChartSmoothing_of_contMDiffAt e h hU hUe
      hrho hG he hh hh' hsupport hfU hrange1 hx
  · exact ⟨(M40.supportedChartSmoothingHomotopy e h hU hUe rho f G
      hrho.continuous hG.continuous hsupport hfU hrange).symm⟩
  · intro x
    by_cases hx : x ∈ tsupport rho
    · change dist (M40.chartPerturb h U f displacement x) (f x) < epsilon
      rw [M40.chartPerturb_of_mem h U f displacement (hsupport hx)]
      simpa using (hcontrol' 1 x hx).2
    · have hEq := M40.supportedChartSmoothing_eventuallyEq e h U rho f G hfU hx
      change dist (M40.supportedChartSmoothing e h U rho f G x) (f x) < epsilon
      rw [hEq.self_of_nhds, dist_self]
      exact hepsilon

end PoincareConjecture.M60
