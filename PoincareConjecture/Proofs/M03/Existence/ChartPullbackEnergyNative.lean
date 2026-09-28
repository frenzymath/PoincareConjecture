import PoincareConjecture.Proofs.M03.Existence.ChartLpNative
import Mathlib.MeasureTheory.Function.L2Space








set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

universe u v

namespace PoincareConjecture.ChartLpNative

section ScalarNorm

variable {X : Type v} [MeasurableSpace X] {μ : Measure X}

theorem scalarL2_norm_sq (f : Lp ℝ 2 μ) : ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  calc
    ‖f‖ ^ 2 = inner ℝ f f := (real_inner_self_eq_norm_sq f).symm
    _ = ∫ x, inner ℝ (f x) (f x) ∂μ := L2.inner_def f f
    _ = _ := by simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem scalarToLp_norm_sq {f : X → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [scalarL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

end ScalarNorm

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem chartPullback_memLp (e : OpenPartialHomeomorph M E) {A : Set E}
    (hA : MeasurableSet A) (hAt : A ⊆ e.target) {μ : Measure M} {c : ℝ}
    (hc : 0 < c) (hdom : ENNReal.ofReal c • (volume.restrict A).map e.symm ≤ μ)
    {f : M → ℝ} (hf : MemLp f 2 μ) : MemLp (f ∘ e.symm) 2 (volume.restrict A) :=
  MemLp.ae_eq (chartPullbackL2_toLp_coe e hA hAt hc hdom hf)
    (Lp.memLp (chartPullbackL2 e hA hAt hc hdom (hf.toLp f)))


theorem chartPullback_integral_sq_le (e : OpenPartialHomeomorph M E) {A : Set E}
    (hA : MeasurableSet A) (hAt : A ⊆ e.target) {μ : Measure M} {c : ℝ}
    (hc : 0 < c) (hdom : ENNReal.ofReal c • (volume.restrict A).map e.symm ≤ μ)
    {f : M → ℝ} (hf : MemLp f 2 μ) :
    (∫ z in A, f (e.symm z) ^ 2) ≤
      ‖(chartPullbackL2 e hA hAt hc hdom : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (volume.restrict A))‖ ^ 2 *
        ‖hf.toLp f‖ ^ 2 := by
  let L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (volume.restrict A) := chartPullbackL2 e hA hAt hc hdom
  calc
    _ = ∫ z in A, L (hf.toLp f) z ^ 2 := by
      apply integral_congr_ae
      filter_upwards [chartPullbackL2_toLp_coe e hA hAt hc hdom hf] with z hz
      exact congrArg (fun t : ℝ => t ^ 2) hz.symm
    _ = ‖L (hf.toLp f)‖ ^ 2 := (scalarL2_norm_sq _).symm
    _ ≤ (‖L‖ * ‖hf.toLp f‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        (L.le_opNorm _)
    _ = _ := mul_pow _ _ _

end PoincareConjecture.ChartLpNative
