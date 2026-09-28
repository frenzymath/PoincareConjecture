import PoincareConjecture.Proofs.M34.Mathlib.CutoffIntegralComparison
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.DominatedConvergence











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology BigOperators

namespace MeasureTheory




theorem tendsto_cutoff_coordinate_energy
    {X F ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {U : Set X} (hU : IsOpen U) (q : F →L[ℝ] EuclideanSpace ℝ ι)
    {φ : X → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    {f : ℕ → X → F} {f₀ : X → F} (hf : ∀ k, ContinuousOn (f k) U)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ k x, x ∈ tsupport φ → ‖f k x‖ ≤ B)
    (hpoint : ∀ x ∈ tsupport φ, Tendsto (fun k => f k x) atTop (𝓝 (f₀ x))) :
    Tendsto (fun k => ∑ i, ∫ x, (φ x * q (f k x) i) ^ 2 ∂μ) atTop
      (𝓝 (∑ i, ∫ x, (φ x * q (f₀ x) i) ^ 2 ∂μ)) := by
  let C : ℝ := (‖q‖ * B) ^ 2
  have hC0 : 0 ≤ ‖q‖ * B := mul_nonneg (norm_nonneg _) hB
  have hφ2c : HasCompactSupport (fun x => φ x ^ 2) :=
    hφc.comp_left (g := fun r : ℝ => r ^ 2) (by simp)
  have hφ2U : tsupport (fun x => φ x ^ 2) ⊆ U := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := φ) (g := φ)).trans hφU
  have hmajorant : Integrable (fun x => φ x ^ 2 * C) μ :=
    integrable_cutoff_mul hU ((hφ.pow 2).continuousOn) hφ2c hφ2U continuousOn_const
  apply tendsto_finsetSum
  intro i _hi
  apply tendsto_integral_of_dominated_convergence (fun x => φ x ^ 2 * C)
  · intro k
    have hc : ContinuousOn (fun x => q (f k x) i) U :=
      (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).continuous.comp_continuousOn
        (q.continuous.comp_continuousOn (hf k))
    have hw : Continuous (fun x => φ x * q (f k x) i) :=
      (hφ.continuousOn.mul hc).continuous_of_tsupport_subset hU
        (tsupport_mul_subset_left.trans hφU)
    exact (hw.pow 2).aestronglyMeasurable
  · exact hmajorant
  · intro k
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hc : |q (f k x) i| ≤ ‖q‖ * B :=
        (PiLp.norm_apply_le (q (f k x)) i).trans
          ((q.le_opNorm (f k x)).trans
            (mul_le_mul_of_nonneg_left (hbound k x hx) (norm_nonneg _)))
      have hs : q (f k x) i ^ 2 ≤ C :=
        sq_le_sq.mpr (hc.trans (le_of_eq (abs_of_nonneg hC0).symm))
      rw [Real.norm_of_nonneg (sq_nonneg _), mul_pow]
      exact mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0),
        norm_zero, le_refl]
  · apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hc : Tendsto (fun k => q (f k x) i) atTop (𝓝 (q (f₀ x) i)) :=
        (((EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).comp q).continuous.tendsto
          (f₀ x)).comp (hpoint x hx)
      exact (hc.const_mul (φ x)).pow 2
    · simpa only [image_eq_zero_of_notMem_tsupport hx, zero_mul,
        zero_pow (by decide : (2 : ℕ) ≠ 0)] using
        (tendsto_const_nhds (x := (0 : ℝ)) (f := (atTop : Filter ℕ)))

end MeasureTheory
