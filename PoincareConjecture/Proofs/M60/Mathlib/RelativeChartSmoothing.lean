import PoincareConjecture.Proofs.M60.Mathlib.ChartApproximation
import PoincareConjecture.Proofs.M40.Mathlib.SupportedChartSmoothing











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M60

variable {E F N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace N] [ChartedSpace F N]




theorem exists_relative_chart_smoothing
    (h : OpenPartialHomeomorph N F)
    (hh : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ h h.source)
    (hh' : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ h.symm h.target)
    (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hrho01 : ∀ x, rho x ∈ Icc 0 1) (hK : IsCompact (tsupport rho))
    (f : C(E, N)) (hfK : MapsTo f (tsupport rho) h.source)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ g : C(E, N),
      (∀ x, dist (g x) (f x) < epsilon) ∧
      (∀ x, x ∉ tsupport rho → g x = f x) ∧
      (∀ x, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) 1 f x →
        ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) 1 g x) ∧
      (∀ x, rho =ᶠ[𝓝 x] 1 → ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g x) := by
  let e := OpenPartialHomeomorph.refl E
  let U := f ⁻¹' h.source
  have hU : IsOpen U := h.open_source.preimage f.continuous
  have hUe : U ⊆ e.source := subset_univ _
  have hsupport : tsupport rho ⊆ U := hfK
  have hfU : MapsTo f U h.source := fun _ hx => hx
  have hcoord : ContinuousOn (h ∘ f) (tsupport rho) :=
    h.continuousOn.comp f.continuous.continuousOn hfK
  have himage : IsCompact ((h ∘ f) '' tsupport rho) := hK.image_of_continuousOn hcoord
  obtain ⟨delta, hdelta, hcontrol⟩ := exists_pos_inverse_chart_control h himage
    (by rintro _ ⟨x, hx, rfl⟩; exact h.map_source (hfK hx)) hepsilon
  obtain ⟨G, hG, hGclose⟩ := exists_contDiff_approx_on_isClosed (isClosed_tsupport rho)
    hcoord hdelta
  let displacement := M40.chartSmoothingDisplacement e h rho f G
  let q := M40.cutoffBlend rho (h ∘ f) G
  have hq (x : E) : h (f x) + displacement x = q x := by
    change h (f x) + rho x • (G x - h (f x)) =
      rho x • G x + (1 - rho x) • h (f x)
    module
  have hqclose (x : E) (hx : x ∈ tsupport rho) : dist (q x) (h (f x)) < delta :=
    (M40.cutoffBlend_dist_le (hrho01 x) le_rfl).trans_lt (hGclose x hx)
  have hqcontrol (x : E) (hx : x ∈ tsupport rho) :
      q x ∈ h.target ∧ dist (h.symm (q x)) (f x) < epsilon := by
    have hc := hcontrol (h (f x)) (mem_image_of_mem (h ∘ f) hx) (q x) (hqclose x hx)
    rwa [h.left_inv (hfK hx)] at hc
  have hrange (x : E) (hx : x ∈ U) : h (f x) + displacement x ∈ h.target := by
    by_cases hxs : x ∈ tsupport rho
    · rw [hq]
      exact (hqcontrol x hxs).1
    · have hr0 := image_eq_zero_of_notMem_tsupport hxs
      simp only [displacement, M40.chartSmoothingDisplacement, hr0, zero_smul, add_zero]
      exact h.map_source (hfU hx)
  let g := M40.supportedChartSmoothing e h U rho f G
  have hg : Continuous g := M40.continuous_supportedChartSmoothing e h hU hUe
    hrho.continuous f.continuous hG.continuous hsupport hfU hrange
  have hagree (x : E) (hx : x ∉ tsupport rho) : g =ᶠ[𝓝 x] f :=
    M40.supportedChartSmoothing_eventuallyEq e h U rho f G hfU hx
  refine ⟨⟨g, hg⟩, ?_, (fun x hx => (hagree x hx).self_of_nhds), ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ tsupport rho
    · change dist (M40.supportedChartSmoothing e h U rho f G x) (f x) < epsilon
      rw [M40.supportedChartSmoothing_of_mem e h U rho f G (hsupport hx)]
      exact (hqcontrol x hx).2
    · change dist (g x) (f x) < epsilon
      rw [(hagree x hx).self_of_nhds, dist_self]
      exact hepsilon
  · intro x hx
    change ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) 1 g x
    by_cases hxU : x ∈ U
    · have hhf := (((hh (f x) (hfU hxU)).contMDiffAt
        (h.open_source.mem_nhds (hfU hxU))).of_le (by simp)).comp x hx
      have hblend : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) 1
          (fun y => h (f y) + displacement y) x := by
        have hrho1 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 rho x :=
          hrho.contMDiff.contMDiffAt.of_le (by simp)
        have hG1 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) 1 G x :=
          hG.contMDiff.contMDiffAt.of_le (by simp)
        exact hhf.add (hrho1.smul (hG1.sub hhf))
      have hi := (((hh' _ (hrange x hxU)).contMDiffAt
        (h.open_target.mem_nhds (hrange x hxU))).of_le (by simp)).comp x hblend
      apply hi.congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hxU] with y hy
      exact M40.chartPerturb_of_mem h U f displacement hy
    · exact hx.congr_of_eventuallyEq (hagree x (fun hs => hxU (hsupport hs)))
  · intro x hx
    exact M40.contMDiffAt_supportedChartSmoothing_of_eventuallyEq_one e h hU hUe hG
      contMDiffOn_id hh' hsupport hrange hx

end PoincareConjecture.M60
