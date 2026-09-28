import PoincareConjecture.Proofs.M10.DivergenceIntegration
import PoincareConjecture.Proofs.M10.SupportedCalculus
import Mathlib.Analysis.Calculus.ContDiff.Comp









set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff BigOperators

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]
  {ι : Type*} [Fintype ι]


theorem integral_mul_trace_fderiv_of_compact_vector
    (b : OrthonormalBasis ι ℝ E) {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} {V : E → E} (hu : ContDiffOn ℝ 1 u U) (hV : ContDiff ℝ 1 V)
    (hc : HasCompactSupport V) (hs : tsupport V ⊆ U) :
    Integrable (fun x ↦ u x * LinearMap.trace ℝ E (fderiv ℝ V x).toLinearMap) μ ∧
      Integrable (fun x ↦ fderiv ℝ u x (V x)) μ ∧
      (∫ x, u x * LinearMap.trace ℝ E (fderiv ℝ V x).toLinearMap ∂μ) =
        -(∫ x, fderiv ℝ u x (V x) ∂μ) := by
  have hdu : ContinuousOn (fderiv ℝ u) U := hu.continuousOn_fderiv_of_isOpen hU le_rfl
  have hdV : Continuous (fderiv ℝ V) := hV.continuous_fderiv one_ne_zero
  have hinner (i : ι) : tsupport (fun x ↦ inner ℝ (b i) (V x)) ⊆ tsupport V :=
    tsupport_comp_subset (g := fun v : E ↦ inner ℝ (b i) v) (by simp) V
  have hinnerD (i : ι) :
      tsupport (fun x ↦ inner ℝ (b i) (fderiv ℝ V x (b i))) ⊆ tsupport V :=
    (tsupport_comp_subset (g := fun v : E ↦ inner ℝ (b i) v) (by simp)
      (fun x ↦ fderiv ℝ V x (b i))).trans (tsupport_fderiv_apply_subset ℝ (b i))
  apply integral_mul_trace_fderiv b
      (fun x hx ↦ (hu.contDiffAt (hU.mem_nhds (hs hx))).differentiableAt one_ne_zero)
      (fun x _ ↦ hV.differentiable one_ne_zero x)
  · intro i
    apply integrable_of_continuousOn_of_tsupport_subset hU hc hs
    · exact (hdu.clm_apply continuousOn_const).mul
        (continuousOn_const.inner hV.continuous.continuousOn)
    · exact tsupport_mul_subset_right.trans (hinner i)
  · intro i
    apply integrable_of_continuousOn_of_tsupport_subset hU hc hs
    · exact hu.continuousOn.mul
        (continuousOn_const.inner ((hdV.clm_apply continuous_const).continuousOn))
    · exact tsupport_mul_subset_right.trans (hinnerD i)
  · intro i
    apply integrable_of_continuousOn_of_tsupport_subset hU hc hs
    · exact hu.continuousOn.mul (continuousOn_const.inner hV.continuous.continuousOn)
    · exact tsupport_mul_subset_right.trans (hinner i)


theorem integral_mul_trace_fderiv_of_compact_scalar
    (b : OrthonormalBasis ι ℝ E) {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} {V : E → E} (hu : ContDiff ℝ 1 u) (hV : ContDiffOn ℝ 1 V U)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ U) :
    Integrable (fun x ↦ u x * LinearMap.trace ℝ E (fderiv ℝ V x).toLinearMap) μ ∧
      Integrable (fun x ↦ fderiv ℝ u x (V x)) μ ∧
      (∫ x, u x * LinearMap.trace ℝ E (fderiv ℝ V x).toLinearMap ∂μ) =
        -(∫ x, fderiv ℝ u x (V x) ∂μ) := by
  have hdu : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hdV : ContinuousOn (fderiv ℝ V) U := hV.continuousOn_fderiv_of_isOpen hU le_rfl
  apply integral_mul_trace_fderiv b
      (fun x _ ↦ hu.differentiable one_ne_zero x)
      (fun x hx ↦ (hV.contDiffAt (hU.mem_nhds (hs hx))).differentiableAt one_ne_zero)
  · intro i
    apply integrable_of_continuousOn_of_tsupport_subset hU hc hs
    · exact (hdu.clm_apply continuous_const).continuousOn.mul
        (continuousOn_const.inner hV.continuousOn)
    · exact tsupport_mul_subset_left.trans (tsupport_fderiv_apply_subset ℝ (b i))
  · intro i
    apply integrable_of_continuousOn_of_tsupport_subset hU hc hs
    · exact hu.continuous.continuousOn.mul
        (continuousOn_const.inner (hdV.clm_apply continuousOn_const))
    · exact tsupport_mul_subset_left
  · intro i
    apply integrable_of_continuousOn_of_tsupport_subset hU hc hs
    · exact hu.continuous.continuousOn.mul (continuousOn_const.inner hV.continuousOn)
    · exact tsupport_mul_subset_left

end PoincareConjecture.M10
