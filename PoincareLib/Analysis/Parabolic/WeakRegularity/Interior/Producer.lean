/-
Adapted from AxelWorkspace revision f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e.
Source and SHA-256: references/analysis/axel-workspace/weak-parabolic-regularity-sources.json.
Apache-2.0; see the license in that source directory.
-/
import PoincareLib.Analysis.Parabolic.WeakRegularity.AdjointIdentity
import PoincareLib.Analysis.Convolution.ConvolutionCommutator

/-!
# Euclidean interior regularity producer: canonical local interface

This module records the two analytic reductions needed by the interior
regularity argument.  First, the canonical distributional equation localizes
to every smaller open set.  Second, once a classical representative is
available, the published adjoint identity identifies the distributional
equation with the pointwise canonical operator.  No solver, heat kernel, or
regularity theorem is hidden in these reductions.

Mollification and derivative estimates are proved in the dependent energy
and weak-jet modules. `WeakRegularity.Smooth` combines them with Sobolev
embedding for the full weak-to-smooth theorem.
-/

open MeasureTheory Set
open scoped ContDiff Topology NNReal Convolution

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ} {U V : Set (Spacetime n)}

local instance : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

/-! ## Actual space-time convolution and translated tests

The convolution below is the ordinary Lebesgue convolution on
`Spacetime n = Euclid n × ℝ`; no abstract distribution or representative is
used.  The second theorem is the exact translated-kernel identity obtained by
testing the canonical weak equation.  Its interior-buffer hypothesis is what
allows the compact kernel support to stay inside the original open set.
-/

/-- Ordinary Lebesgue space-time convolution, written with the kernel on the
left. -/
def lebesgueConvolution (η u : Spacetime n → ℝ) (z : Spacetime n) : ℝ :=
  ∫ y, η (z - y) * u y

theorem lebesgueConvolution_eq_convolution (η u : Spacetime n → ℝ) :
    lebesgueConvolution η u = η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u := by
  funext z
  rw [convolution_lsmul_swap]
  rfl

/-- The translated kernel used to test at a fixed space-time point. -/
def translatedKernel (η : Spacetime n → ℝ) (z : Spacetime n) : Spacetime n → ℝ :=
  fun y => η (z - y)

/-! The first genuinely variable-coefficient step.  We keep the convolution
in its literal Lebesgue form so that no abstract distribution or smooth
representative is involved. -/

theorem lebesgueConvolution_coefficient_commutator_eq
    {q f η : Spacetime n → ℝ} (hq : Continuous q) (hf : Continuous f)
    (hη : Continuous η) (hηc : HasCompactSupport η) (z : Spacetime n) :
    q z * lebesgueConvolution η f z -
        lebesgueConvolution η (fun y => q y * f y) z =
      ∫ y, η (z - y) * (q z - q y) * f y := by
  let e : Spacetime n → Spacetime n := fun y => z - y
  have he : Continuous e := continuous_const.sub continuous_id
  have hηz : HasCompactSupport (fun y => η (z - y)) :=
    hηc.comp_homeomorph (Homeomorph.subLeft z)
  have h₁ : Integrable (fun y => q z * (η (z - y) * f y)) :=
    (((hη.comp he).mul hf).const_mul (q z)).integrable_of_hasCompactSupport
      hηz.mul_right.mul_left
  have h₂ : Integrable (fun y => η (z - y) * (q y * f y)) :=
    ((hη.comp he).mul (hq.mul hf)).integrable_of_hasCompactSupport hηz.mul_right
  simp only [lebesgueConvolution]
  rw [← integral_const_mul, ← integral_sub h₁ h₂]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

theorem abs_le_lebesgueConvolution_coefficient_commutator
    {q f η : Spacetime n → ℝ} {L : ℝ≥0} {B : ℝ}
    (hq : LipschitzWith L q) (hf : Continuous f) (hB : ∀ y, |f y| ≤ B)
    (hη : Continuous η) (hηc : HasCompactSupport η) (z : Spacetime n) :
    |q z * lebesgueConvolution η f z -
        lebesgueConvolution η (fun y => q y * f y) z| ≤
      (L : ℝ) * B * ∫ y, ‖z - y‖ * |η (z - y)| := by
  simp only [lebesgueConvolution_eq_convolution]
  rw [integral_sub_left_eq_self (fun y => ‖y‖ * |η y|) volume z]
  exact Poincare.Analysis.Convolution.abs_convolution_coefficient_commutator_le
    volume hq hf hB hη hηc z

theorem WeakSolutionOn.translatedKernel_pairing_zero
    {C : Coefficients n} {u : Spacetime n → ℝ}
    (hu : WeakSolutionOn C u U) {η : Spacetime n → ℝ}
    (hη : ContDiff ℝ ∞ η)
    {V : Set (Spacetime n)}
    (hηc : ∀ z ∈ V, HasCompactSupport (translatedKernel η z))
    (hηU : ∀ z ∈ V, tsupport (translatedKernel η z) ⊆ U) :
    ∀ z ∈ V, (∫ y, u y * C.adjoint (translatedKernel η z) y) = 0 := by
  intro z hz
  have hηz : ContDiff ℝ ∞ (translatedKernel η z) := by
    change ContDiff ℝ ∞ (η ∘ fun y => z - y)
    exact hη.comp (contDiff_const.sub contDiff_id)
  exact hu.2 (translatedKernel η z) hηz
    (hηc z hz)
    (hηU z hz)

/-! The same identity with the adjoint expanded.  Keeping this form explicit
is useful when the coefficient differences are estimated in the mollification
commutator argument. -/

theorem WeakSolutionOn.translatedKernel_adjoint_expanded_zero
    {C : Coefficients n} {u : Spacetime n → ℝ}
    (hu : WeakSolutionOn C u U) {η : Spacetime n → ℝ}
    (hη : ContDiff ℝ ∞ η)
    {V : Set (Spacetime n)}
    (hηc : ∀ z ∈ V, HasCompactSupport (translatedKernel η z))
    (hηU : ∀ z ∈ V, tsupport (translatedKernel η z) ⊆ U) :
    ∀ z ∈ V,
      (∫ y, u y *
        (-timeDeriv (translatedKernel η z) y -
          (∑ i, ∑ j, spatialDeriv j (spatialDeriv i
            (fun w => C.principal i j w * translatedKernel η z w)) y) -
          (∑ i, spatialDeriv i
            (fun w => C.drift i w * translatedKernel η z w) y) +
          C.zeroth y * translatedKernel η z y)) = 0 := by
  intro z hz
  simpa only [Coefficients.adjoint] using
    hu.translatedKernel_pairing_zero hη hηc hηU z hz

@[simp] theorem lebesgueConvolution_eq_integral (η u : Spacetime n → ℝ)
    (z : Spacetime n) :
    lebesgueConvolution η u z = ∫ y, η (z - y) * u y := rfl

/-- A canonical weak solution remains a canonical weak solution after
restriction to a smaller open region.  The test support is already compact,
so the original weak identity can be reused verbatim. -/
theorem WeakSolutionOn.restrict (hV : IsOpen V) (hVU : V ⊆ U)
    {C : Coefficients n} {u : Spacetime n → ℝ}
    (hu : WeakSolutionOn C u U) : WeakSolutionOn C u V := by
  refine ⟨?_, ?_⟩
  · exact hu.1.mono_set hVU
  · intro φ hφ hφc hφV
    exact hu.2 φ hφ hφc (hφV.trans hVU)

/-! The analytic difference-quotient argument produces one finite-order
regularity statement at a time.  This bridge keeps that family attached to the
same original function and region for the final smoothness conclusion. -/

theorem contDiffOn_of_all_finite_orders
    {u : Spacetime n → ℝ}
    (hregular : ∀ m : ℕ, ContDiffOn ℝ m u U) :
    ContDiffOn ℝ ∞ u U := by
  exact contDiffOn_infty.mpr hregular

/-- The canonical adjoint pairing yields the pointwise equation whenever the
candidate is already smooth on the open region.  This is the exact direction
used after an independent interior smoothing proof has supplied a smooth
representative. -/
theorem operator_eq_zero_of_weakSolutionOn
    (hU : IsOpen U) (C : Coefficients n) (hC : C.IsSmoothOn U)
    {u : Spacetime n → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hweak : WeakSolutionOn C u U) :
    ∀ z ∈ U, C.operator u z = 0 := by
  exact (weakSolutionOn_iff_operator_eq_zero hU C hC hu).mp hweak

/-- Conversely, a smooth pointwise solution satisfies the canonical
distributional equation, with no auxiliary representative or solver. -/
theorem weakSolutionOn_of_operator_eq_zero
    (hU : IsOpen U) (C : Coefficients n) (hC : C.IsSmoothOn U)
    {u : Spacetime n → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hop : ∀ z ∈ U, C.operator u z = 0) :
    WeakSolutionOn C u U := by
  exact (weakSolutionOn_iff_operator_eq_zero hU C hC hu).mpr hop

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
