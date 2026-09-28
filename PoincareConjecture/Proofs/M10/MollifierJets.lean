import PoincareConjecture.Proofs.M10.MollifierBasics

set_option autoImplicit false

open MeasureTheory Filter ContinuousLinearMap
open scoped ContDiff Convolution Topology

namespace PoincareConjecture.M10

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

noncomputable local instance mollifierJetNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance mollifierJetNormedSpace :
    NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

noncomputable local instance mollifierSecondJetNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance mollifierSecondJetNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

omit [CompleteSpace F] in

theorem fderiv_normed_convolution (κ : ContDiffBump (0 : E)) {f : E → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (x : E) :
    fderiv ℝ (κ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x =
      (κ.normed μ ⋆[lsmul ℝ ℝ, μ] fderiv ℝ f) x := by
  have hpre : (lsmul ℝ ℝ (E := F)).precompR E = lsmul ℝ ℝ (E := E →L[ℝ] F) := by
    ext c A
    rfl
  have hk : LocallyIntegrable (κ.normed μ) μ :=
    (κ.continuous_normed (μ := μ)).locallyIntegrable
  have h := (hc.hasFDerivAt_convolution_right (lsmul ℝ ℝ)
    hk hf x).fderiv
  simpa only [hpre] using h

omit [CompleteSpace F] in

theorem second_fderiv_normed_convolution (κ : ContDiffBump (0 : E)) {f : E → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 2 f) (x : E) :
    fderiv ℝ (fderiv ℝ (κ.normed μ ⋆[lsmul ℝ ℝ, μ] f)) x =
      (κ.normed μ ⋆[lsmul ℝ ℝ, μ] fderiv ℝ (fderiv ℝ f)) x := by
  have hfirst : fderiv ℝ (κ.normed μ ⋆[lsmul ℝ ℝ, μ] f) =
      κ.normed μ ⋆[lsmul ℝ ℝ, μ] fderiv ℝ f :=
    funext (fderiv_normed_convolution κ hc (hf.of_le (by norm_num)))
  rw [hfirst]
  exact fderiv_normed_convolution κ (hc.fderiv ℝ) (hf.fderiv_right (by norm_num)) x

theorem normed_convolution_jets_tendsto {κ : ℕ → ContDiffBump (0 : E)}
    (hκ : Tendsto (fun j ↦ (κ j).rOut) atTop (𝓝 0)) {f : E → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 2 f) (x : E) :
    Tendsto (fun j ↦ ((κ j).normed μ ⋆[lsmul ℝ ℝ, μ] f) x) atTop (𝓝 (f x)) ∧
    Tendsto (fun j ↦ fderiv ℝ ((κ j).normed μ ⋆[lsmul ℝ ℝ, μ] f) x)
      atTop (𝓝 (fderiv ℝ f x)) ∧
    Tendsto (fun j ↦ fderiv ℝ (fderiv ℝ ((κ j).normed μ ⋆[lsmul ℝ ℝ, μ] f)) x)
      atTop (𝓝 (fderiv ℝ (fderiv ℝ f) x)) := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  refine ⟨ContDiffBump.convolution_tendsto_right_of_continuous hκ hf.continuous x, ?_, ?_⟩
  · simpa only [fderiv_normed_convolution _ hc (hf.of_le (by norm_num))] using
      (ContDiffBump.convolution_tendsto_right_of_continuous (μ := μ) hκ
        (hf.continuous_fderiv (by norm_num)) x)
  · simpa only [second_fderiv_normed_convolution _ hc hf] using
      (ContDiffBump.convolution_tendsto_right_of_continuous (μ := μ) hκ
        (hdf.continuous_fderiv one_ne_zero) x)

end PoincareConjecture.M10
