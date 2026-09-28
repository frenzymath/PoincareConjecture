import PoincareConjecture.Proofs.M40.Mathlib.LipschitzSmoothingLocal
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Coefficients
import PoincareConjecture.Definitions.M60Area










set_option autoImplicit false

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology ContDiff Convolution

noncomputable section

namespace PoincareConjecture.M60

variable {n : ℕ}




theorem suC1_compact_extension
    {f : LoopPlane → EuclideanSpace ℝ (Fin n)} {K U : Set LoopPlane}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) :
    ∃ F : LoopPlane → EuclideanSpace ℝ (Fin n),
      ContDiff ℝ 1 F ∧ HasCompactSupport F ∧
        ∃ r : ℝ, 0 < r ∧ EqOn F f (cthickening r K) := by
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨chi, hchi, hchic, -, hchi1, hchis⟩ :=
    Poincare.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff
      hK.cthickening hU hrU
  let F : LoopPlane → EuclideanSpace ℝ (Fin n) := fun x => chi x • f x
  have hF : ContDiff ℝ 1 F := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport chi
    · exact (hchi.of_le (by simp)).contDiffAt.smul
        ((hf x (hchis hx)).contDiffAt (hU.mem_nhds (hchis hx)))
    · apply (contDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin n)))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [F, hy, Pi.zero_apply, zero_smul]
  refine ⟨F, hF, hchic.smul_right, r, hr, ?_⟩
  intro x hx
  simp only [F, hchi1 x hx, one_smul]



theorem suC1_normalizedConvolution_fderiv
    {f : LoopPlane → EuclideanSpace ℝ (Fin n)}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (phi : ContDiffBump (0 : LoopPlane)) (x : LoopPlane) :
    fderiv ℝ (M40.normalizedConvolution volume phi f) x =
      M40.normalizedConvolution volume phi (fderiv ℝ f) x := by
  have h := hc.hasFDerivAt_convolution_right (μ := volume) (lsmul ℝ ℝ)
    ((phi.continuous_normed (μ := volume)).locallyIntegrable) hf x
  exact h.fderiv



theorem suC1_compactSupport_smooth_approximation
    {f : LoopPlane → EuclideanSpace ℝ (Fin n)}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ G : LoopPlane → EuclideanSpace ℝ (Fin n), ContDiff ℝ ∞ G ∧
      (∀ x, dist (G x) (f x) < epsilon) ∧
      ∀ x, dist (fderiv ℝ G x) (fderiv ℝ f x) < epsilon := by
  obtain ⟨r0, hr0, h0⟩ := M40.exists_radius_normalizedConvolution_dist_lt_uniform
    (μ := volume) (hc.uniformContinuous_of_continuous hf.continuous) hepsilon
  obtain ⟨r1, hr1, h1⟩ := M40.exists_radius_normalizedConvolution_dist_lt_uniform
    (μ := volume) ((hc.fderiv ℝ).uniformContinuous_of_continuous
      (hf.continuous_fderiv (by simp))) hepsilon
  let r : ℝ := min r0 r1 / 2
  have hr : 0 < r := half_pos (lt_min hr0 hr1)
  let phi : ContDiffBump (0 : LoopPlane) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hr0' : phi.rOut ≤ r0 :=
    (half_lt_self (lt_min hr0 hr1)).le.trans (min_le_left _ _)
  have hr1' : phi.rOut ≤ r1 :=
    (half_lt_self (lt_min hr0 hr1)).le.trans (min_le_right _ _)
  refine ⟨M40.normalizedConvolution volume phi f,
    M40.normalizedConvolution_contDiff phi hf.continuous.locallyIntegrable,
    h0 phi hr0', ?_⟩
  intro x
  rw [suC1_normalizedConvolution_fderiv hf hc]
  exact h1 phi hr1' x




theorem suC1_smooth_approximation_on_compact
    {f : LoopPlane → EuclideanSpace ℝ (Fin n)} {K U : Set LoopPlane}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ G : LoopPlane → EuclideanSpace ℝ (Fin n), ContDiff ℝ ∞ G ∧
      ∀ x ∈ K, dist (G x) (f x) < epsilon ∧
        dist (fderiv ℝ G x) (fderiv ℝ f x) < epsilon := by
  obtain ⟨F, hF, hFc, r, hr, hEq⟩ := suC1_compact_extension hK hU hKU hf
  obtain ⟨G, hG, hG0, hG1⟩ := suC1_compactSupport_smooth_approximation hF hFc hepsilon
  refine ⟨G, hG, ?_⟩
  intro x hx
  have hnear : F =ᶠ[𝓝 x] f := by
    filter_upwards [isOpen_thickening.mem_nhds (self_subset_thickening hr K hx)] with y hy
    exact hEq (thickening_subset_cthickening _ _ hy)
  rw [← hnear.self_of_nhds, ← hnear.fderiv_eq]
  exact ⟨hG0 x, hG1 x⟩




theorem suC1_smooth_approximation_jet_observable
    {f : LoopPlane → EuclideanSpace ℝ (Fin n)} {K U : Set LoopPlane}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ 1 f U)
    (Phi : LoopPlane × (EuclideanSpace ℝ (Fin n) ×
      (LoopPlane →L[ℝ] EuclideanSpace ℝ (Fin n))) → ℝ)
    (hPhi : ∀ x ∈ K, ContinuousAt Phi (x, f x, fderiv ℝ f x))
    {epsilon eta : ℝ} (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ G : LoopPlane → EuclideanSpace ℝ (Fin n), ContDiff ℝ ∞ G ∧
      (∀ x ∈ K, dist (G x) (f x) < epsilon) ∧
      ∀ x ∈ K, dist (Phi (x, G x, fderiv ℝ G x))
        (Phi (x, f x, fderiv ℝ f x)) < eta := by
  let j := fun x => (x, f x, fderiv ℝ f x)
  have hj : ContinuousOn j K := by
    apply continuousOn_id.prodMk
    apply (hf.continuousOn.mono hKU).prodMk
    intro x hx
    exact (((hf x (hKU hx)).contDiffAt (hU.mem_nhds (hKU hx))).continuousAt_fderiv
      (by simp)).continuousWithinAt
  have hcompact : IsCompact (j '' K) := hK.image_of_continuousOn hj
  have hu := hcompact.uniformContinuousAt_of_continuousAt Phi
    (by rintro _ ⟨x, hx, rfl⟩; exact hPhi x hx) (dist_mem_uniformity heta)
  obtain ⟨delta, hdelta, hcontrol⟩ := mem_uniformity_dist.mp hu
  obtain ⟨G, hG, hclose⟩ := suC1_smooth_approximation_on_compact hK hU hKU hf
    (lt_min hepsilon hdelta)
  refine ⟨G, hG, fun x hx => (hclose x hx).1.trans_le (min_le_left _ _), ?_⟩
  intro x hx
  have hd : dist (j x) (x, G x, fderiv ℝ G x) < delta := by
    simp only [j, Prod.dist_eq, dist_self, max_lt_iff]
    exact ⟨hdelta, by
      rw [dist_comm]
      exact (hclose x hx).1.trans_le (min_le_right _ _), by
      rw [dist_comm]
      exact (hclose x hx).2.trans_le (min_le_right _ _)⟩
  have hh : dist (Phi (j x)) (Phi (x, G x, fderiv ℝ G x)) < eta :=
    hcontrol hd (mem_image_of_mem j hx)
  simpa only [j, dist_comm] using hh

end PoincareConjecture.M60

end
