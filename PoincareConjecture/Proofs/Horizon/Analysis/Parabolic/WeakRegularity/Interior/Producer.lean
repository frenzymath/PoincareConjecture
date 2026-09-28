import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.AdjointIdentity
import PoincareConjecture.Proofs.Horizon.Analysis.Convolution.ConvolutionCommutator

open MeasureTheory Set
open scoped ContDiff Topology NNReal Convolution

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ} {U V : Set (Spacetime n)}

local instance : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

def lebesgueConvolution (η u : Spacetime n → ℝ) (z : Spacetime n) : ℝ :=
  ∫ y, η (z - y) * u y

theorem lebesgueConvolution_eq_convolution (η u : Spacetime n → ℝ) :
    lebesgueConvolution η u = η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u := by
  funext z
  rw [convolution_lsmul_swap]
  rfl

def translatedKernel (η : Spacetime n → ℝ) (z : Spacetime n) : Spacetime n → ℝ :=
  fun y => η (z - y)

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

theorem WeakSolutionOn.restrict (hV : IsOpen V) (hVU : V ⊆ U)
    {C : Coefficients n} {u : Spacetime n → ℝ}
    (hu : WeakSolutionOn C u U) : WeakSolutionOn C u V := by
  refine ⟨?_, ?_⟩
  · exact hu.1.mono_set hVU
  · intro φ hφ hφc hφV
    exact hu.2 φ hφ hφc (hφV.trans hVU)

theorem contDiffOn_of_all_finite_orders
    {u : Spacetime n → ℝ}
    (hregular : ∀ m : ℕ, ContDiffOn ℝ m u U) :
    ContDiffOn ℝ ∞ u U := by
  exact contDiffOn_infty.mpr hregular

theorem operator_eq_zero_of_weakSolutionOn
    (hU : IsOpen U) (C : Coefficients n) (hC : C.IsSmoothOn U)
    {u : Spacetime n → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hweak : WeakSolutionOn C u U) :
    ∀ z ∈ U, C.operator u z = 0 := by
  exact (weakSolutionOn_iff_operator_eq_zero hU C hC hu).mp hweak

theorem weakSolutionOn_of_operator_eq_zero
    (hU : IsOpen U) (C : Coefficients n) (hC : C.IsSmoothOn U)
    {u : Spacetime n → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hop : ∀ z ∈ U, C.operator u z = 0) :
    WeakSolutionOn C u U := by
  exact (weakSolutionOn_iff_operator_eq_zero hU C hC hu).mpr hop

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
