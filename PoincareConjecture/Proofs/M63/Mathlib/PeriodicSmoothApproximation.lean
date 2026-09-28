import PoincareConjecture.Proofs.M63.Mathlib.PeriodicTranslation
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral









set_option autoImplicit false

open Set Filter MeasureTheory ContinuousLinearMap
open scoped ContDiff Convolution Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem Function.Periodic.deriv_of_differentiable
    {f : ℝ → E} {P : ℝ} (hp : Function.Periodic f P)
    (hf : Differentiable ℝ f) : Function.Periodic (deriv f) P := by
  intro x
  have hd : HasDerivAt (fun y => f (y + P)) (deriv f (x + P)) x := by
    simpa only [Function.comp_def, one_smul, id_eq] using
      (hf (x + P)).hasDerivAt.scomp x ((hasDerivAt_id x).add_const P)
  rw [show (fun y => f (y + P)) = f from funext hp] at hd
  exact hd.unique (hf x).hasDerivAt




theorem ContDiffBump.hasDerivAt_normed_convolution [CompleteSpace E]
    (φ : ContDiffBump (0 : ℝ)) {f g : ℝ → E}
    (hf : Continuous f) (hg : Continuous g) {C : ℝ}
    (hC : ∀ y, ‖g y‖ ≤ C) (hd : ∀ y, HasDerivAt f (g y) y) (x : ℝ) :
    HasDerivAt (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f)
      ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) x) x := by
  have hi (u : ℝ → E) (hu : Continuous u) (z : ℝ) :
      Integrable (fun s : ℝ => φ.normed volume s • u (z - s)) :=
    ((φ.hasCompactSupport_normed.convolutionExists_left
      (lsmul ℝ ℝ) φ.continuous_normed hu.locallyIntegrable) z).integrable
  have hF : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable
      (fun s : ℝ => φ.normed volume s • f (z - s)) volume :=
    Eventually.of_forall (fun z => (hi f hf z).aestronglyMeasurable)
  have hbound : ∀ᵐ s : ℝ, ∀ z ∈ (univ : Set ℝ),
      ‖φ.normed volume s • g (z - s)‖ ≤ φ.normed volume s * C := by
    filter_upwards [] with s z _
    rw [norm_smul, Real.norm_of_nonneg (φ.nonneg_normed s)]
    exact mul_le_mul_of_nonneg_left (hC (z - s)) (φ.nonneg_normed s)
  have hdiff : ∀ᵐ s : ℝ, ∀ z ∈ (univ : Set ℝ),
      HasDerivAt (fun y => φ.normed volume s • f (y - s))
        (φ.normed volume s • g (z - s)) z := by
    filter_upwards [] with s z _
    have hshift : HasDerivAt (fun y => f (y - s)) (g (z - s)) z := by
      simpa only [Function.comp_def, one_smul, id_eq] using
        (hd (z - s)).scomp z ((hasDerivAt_id z).sub_const s)
    exact hshift.const_smul (φ.normed volume s)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := univ) (F := fun z s : ℝ => φ.normed volume s • f (z - s))
    (F' := fun z s : ℝ => φ.normed volume s • g (z - s))
    (bound := fun s : ℝ => φ.normed volume s * C)
    univ_mem hF (hi f hf x) (hi g hg x).aestronglyMeasurable hbound
    (φ.integrable_normed.mul_const C) hdiff).2

namespace PoincareConjecture.M63




theorem exists_periodic_smooth_C2_approximation [CompleteSpace E]
    {P : ℝ} (hP : 0 < P) {c : ℝ → E}
    (hc : ContDiff ℝ 2 c) (hp : Function.Periodic c P)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ r : ℝ → E, ContDiff ℝ ∞ r ∧ Function.Periodic r P ∧
      ∀ x, ‖r x - c x‖ < eps ∧
        ‖deriv r x - deriv c x‖ < eps ∧
        ‖deriv (deriv r) x - deriv (deriv c) x‖ < eps := by
  let : Fact (0 < P) := ⟨hP⟩
  have hc₁ : ContDiff ℝ 1 (deriv c) := hc.deriv' (n := 1)
  have hd : Differentiable ℝ c := hc.differentiable (by norm_num)
  have hd₁ : Differentiable ℝ (deriv c) := hc₁.differentiable (by norm_num)
  have hp₁ := hp.deriv_of_differentiable hd
  have hp₂ := hp₁.deriv_of_differentiable hd₁
  let f₀ : C(AddCircle P, E) := ⟨hp.lift,
    (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples P)).continuous_iff.mpr
      hc.continuous⟩
  let f₁ : C(AddCircle P, E) := ⟨hp₁.lift,
    (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples P)).continuous_iff.mpr
      hc₁.continuous⟩
  let f₂ : C(AddCircle P, E) := ⟨hp₂.lift,
    (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples P)).continuous_iff.mpr
      hc₁.continuous_deriv_one⟩
  have hmod (f : C(AddCircle P, E)) :
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ → ∀ x : ℝ,
        ‖f ((x - s : ℝ) : AddCircle P) - f (x : AddCircle P)‖ < eps / 2 := by
    have hnorm : Continuous (fun s : ℝ => ‖periodicTranslation s f - f‖) :=
      ((continuous_periodicTranslation.comp
        (continuous_id.prodMk continuous_const)).sub continuous_const).norm
    have hzero : ‖periodicTranslation 0 f - f‖ < eps / 2 := by
      have hsame : periodicTranslation 0 f = f := by
        ext x
        change f (x - (0 : AddCircle P)) = f x
        rw [sub_zero]
      simpa only [hsame, sub_self, norm_zero] using half_pos heps
    obtain ⟨δ, hδ, hnear⟩ := Metric.mem_nhds_iff.mp
      (hnorm.continuousAt.eventually (isOpen_Iio.mem_nhds hzero))
    refine ⟨δ, hδ, fun s hs x => ?_⟩
    have hn : ‖periodicTranslation s f - f‖ < eps / 2 :=
      hnear (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hs)
    have hv := (ContinuousMap.norm_coe_le_norm (periodicTranslation s f - f)
      (x : AddCircle P)).trans_lt hn
    change ‖f ((x : AddCircle P) - (s : AddCircle P)) - f (x : AddCircle P)‖ < eps / 2 at hv
    simpa only [AddCircle.coe_sub] using hv
  obtain ⟨δ₀, hδ₀, hnear₀⟩ := hmod f₀
  obtain ⟨δ₁, hδ₁, hnear₁⟩ := hmod f₁
  obtain ⟨δ₂, hδ₂, hnear₂⟩ := hmod f₂
  let δ := min δ₀ (min δ₁ δ₂)
  have hδ : 0 < δ := lt_min hδ₀ (lt_min hδ₁ hδ₂)
  let φ : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  let r : ℝ → E := φ.normed volume ⋆[lsmul ℝ ℝ, volume] c
  have hr : ContDiff ℝ ∞ r :=
    φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      φ.contDiff_normed hc.continuous.locallyIntegrable
  have hr₁ : deriv r = φ.normed volume ⋆[lsmul ℝ ℝ, volume] deriv c := by
    funext x
    exact (φ.hasDerivAt_normed_convolution hc.continuous hc₁.continuous
      (fun y => ContinuousMap.norm_coe_le_norm f₁ (y : AddCircle P))
      (fun y => (hd y).hasDerivAt) x).deriv
  have hr₂ : deriv (deriv r) =
      φ.normed volume ⋆[lsmul ℝ ℝ, volume] deriv (deriv c) := by
    rw [hr₁]
    funext x
    exact (φ.hasDerivAt_normed_convolution hc₁.continuous hc₁.continuous_deriv_one
      (fun y => ContinuousMap.norm_coe_le_norm f₂ (y : AddCircle P))
      (fun y => (hd₁ y).hasDerivAt) x).deriv
  have hrper : Function.Periodic r P := by
    intro x
    apply integral_congr_ae
    filter_upwards [] with s
    change φ.normed volume s • c (x + P - s) = φ.normed volume s • c (x - s)
    rw [show x + P - s = (x - s) + P by ring, hp]
  have herror (u : ℝ → E) (hu : Continuous u)
      (huδ : ∀ s : ℝ, |s| < δ → ∀ x : ℝ, ‖u (x - s) - u x‖ < eps / 2)
      (x : ℝ) :
      ‖(φ.normed volume ⋆[lsmul ℝ ℝ, volume] u) x - u x‖ < eps := by
    apply lt_of_le_of_lt _ (half_lt_self heps)
    rw [← dist_eq_norm]
    apply φ.dist_normed_convolution_le hu.aestronglyMeasurable
    intro y hy
    have hxy : |x - y| < δ := by
      simpa only [Metric.mem_ball, Real.dist_eq, φ, abs_sub_comm] using hy
    simpa only [sub_sub_cancel, dist_eq_norm] using (huδ (x - y) hxy x).le
  refine ⟨r, hr, hrper, fun x => ⟨?_, ?_, ?_⟩⟩
  · exact herror c hc.continuous (fun s hs y =>
      hnear₀ s (hs.trans_le (min_le_left _ _)) y) x
  · rw [hr₁]
    exact herror (deriv c) hc₁.continuous (fun s hs y =>
      hnear₁ s (hs.trans_le ((min_le_right _ _).trans (min_le_left _ _))) y) x
  · rw [hr₂]
    exact herror (deriv (deriv c)) hc₁.continuous_deriv_one (fun s hs y =>
      hnear₂ s (hs.trans_le ((min_le_right _ _).trans (min_le_right _ _))) y) x

end PoincareConjecture.M63
