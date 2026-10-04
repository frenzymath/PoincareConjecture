import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Smoothing.Euclidean.Approximation
import Mathlib.Topology.UrysohnsLemma

/-!
# Compact coordinate domains for convolution

An open chart need not specify measurable or continuous values away from its
source. Before convolution, multiply its coordinate map by a compactly
supported continuous cutoff which is one near the compact set being
smoothed. The convolution can then be made uniformly close on that compact
set by taking any sufficiently small bump. These are the localization
steps in the SurgeryComparison.Transport quantitative smoothing obligation following Morgan--Tian
Claim 18.22, printed p. 433.
-/

set_option autoImplicit false

open Function Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace PoincareMT.SurgeryComparison.Transport

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Extend a coordinate map continuously to the whole vector space while
preserving it on a closed neighborhood of a specified compact set.
SurgeryComparison.Transport quantitative smoothing, Morgan--Tian Claim 18.22, p. 433. -/
theorem exists_continuous_compactSupport_extension
    {f : E → F} {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hf : ContinuousOn f U) :
    ∃ f' : E → F, Continuous f' ∧ HasCompactSupport f' ∧
      ∃ r : ℝ, 0 < r ∧ EqOn f' f (cthickening r K) := by
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨ρ, hρone, hρcompact, hρsupport, _⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK.cthickening hU hrU
  refine ⟨fun x => ρ x • f x, ?_, ?_, r, hr, ?_⟩
  · exact (ρ.continuous.continuousOn.smul hf).continuous_of_tsupport_subset hU
      ((tsupport_smul_subset_left _ _).trans hρsupport)
  · exact (show HasCompactSupport ρ from hρcompact).smul_right
  · intro x hx
    simp only [hρone hx, Pi.one_apply, one_smul]

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- On a compact set, every sufficiently small normalized convolution is
uniformly close to the original continuous map. The radius is independent
of the shape of the normalized bump. SurgeryComparison.Transport quantitative smoothing,
Morgan--Tian Claim 18.22, p. 433. -/
theorem exists_radius_normalizedConvolution_dist_lt
    {f : E → F} {K : Set E} (hf : Continuous f) (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ φ : ContDiffBump (0 : E), φ.rOut ≤ r →
      ∀ x ∈ K, dist (normalizedConvolution μ φ f x) (f x) < ε := by
  have hu : UniformContinuousOn f (cthickening 1 K) :=
    hK.cthickening.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / 2) (half_pos hε)
  refine ⟨min 1 δ, lt_min one_pos hδ, ?_⟩
  intro φ hφ x hx
  apply (φ.dist_normed_convolution_le hf.aestronglyMeasurable ?_).trans_lt (half_lt_self hε)
  intro y hy
  have hyr : dist y x < min 1 δ := hy.trans_le hφ
  have hyK : y ∈ cthickening 1 K :=
    mem_cthickening_of_dist_le _ x _ _ hx
      (hyr.le.trans (min_le_left _ _))
  have hxK : x ∈ cthickening 1 K := self_subset_cthickening _ hx
  exact (hfδ y hyK x hxK (hyr.trans_le (min_le_right _ _))).le

/-- Choose a smooth convolution satisfying a requested support radius and
a uniform error on a compact set. The explicit bump remains available to
apply the translated finite-difference estimates. SurgeryComparison.Transport quantitative smoothing,
Morgan--Tian Claim 18.22, p. 433. -/
theorem exists_small_normalizedConvolution
    {f : E → F} {K : Set E} (hf : Continuous f) (hK : IsCompact K)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ∃ φ : ContDiffBump (0 : E), φ.rOut < R ∧
      ContDiff ℝ ∞ (normalizedConvolution μ φ f) ∧
      ∀ x ∈ K, dist (normalizedConvolution μ φ f x) (f x) < ε := by
  obtain ⟨r, hr, happrox⟩ :=
    exists_radius_normalizedConvolution_dist_lt (μ := μ) hf hK hε
  let s := min r R / 2
  have hs : 0 < s := half_pos (lt_min hr hR)
  let φ : ContDiffBump (0 : E) := ⟨s / 2, s, half_pos hs, half_lt_self hs⟩
  have hsmin : s < min r R := half_lt_self (lt_min hr hR)
  refine ⟨φ, hsmin.trans_le (min_le_right _ _),
    normalizedConvolution_contDiff φ hf.locallyIntegrable,
    happrox φ (hsmin.le.trans (min_le_left _ _))⟩

/-- Uniform continuity gives a radius controlling normalized convolutions
on the whole coordinate space. The compactly supported coordinate
extension satisfies this hypothesis. SurgeryComparison.Transport quantitative smoothing,
Morgan--Tian Claim 18.22, p. 433. -/
theorem exists_radius_normalizedConvolution_dist_lt_uniform
    {f : E → F} (hf : UniformContinuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ φ : ContDiffBump (0 : E), φ.rOut ≤ r →
      ∀ x, dist (normalizedConvolution μ φ f x) (f x) < ε := by
  obtain ⟨r, hr, hfr⟩ :=
    Metric.uniformContinuous_iff.mp hf (ε / 2) (half_pos hε)
  refine ⟨r, hr, ?_⟩
  intro φ hφ x
  apply (φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable ?_).trans_lt
    (half_lt_self hε)
  intro y hy
  exact (hfr (hy.trans_le hφ)).le

/-- Choose one explicit convolution meeting both a prescribed support
radius and a global coordinate error budget. SurgeryComparison.Transport quantitative smoothing,
Morgan--Tian Claim 18.22, p. 433. -/
theorem exists_small_normalizedConvolution_uniform
    {f : E → F} (hf : UniformContinuous f)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ∃ φ : ContDiffBump (0 : E), φ.rOut < R ∧
      ContDiff ℝ ∞ (normalizedConvolution μ φ f) ∧
      ∀ x, dist (normalizedConvolution μ φ f x) (f x) < ε := by
  obtain ⟨r, hr, happrox⟩ :=
    exists_radius_normalizedConvolution_dist_lt_uniform (μ := μ) hf hε
  let s := min r R / 2
  have hs : 0 < s := half_pos (lt_min hr hR)
  let φ : ContDiffBump (0 : E) := ⟨s / 2, s, half_pos hs, half_lt_self hs⟩
  have hsmin : s < min r R := half_lt_self (lt_min hr hR)
  refine ⟨φ, hsmin.trans_le (min_le_right _ _),
    normalizedConvolution_contDiff φ hf.continuous.locallyIntegrable,
    happrox φ (hsmin.le.trans (min_le_left _ _))⟩

end PoincareMT.SurgeryComparison.Transport
