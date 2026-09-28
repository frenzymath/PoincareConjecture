import PoincareConjecture.Proofs.M35.RadialGauge.HeatSmoothness
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem heatAverage_time_continuous {f : V → F} (hf : Continuous f)
    {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) (x : V) :
    Continuous (fun t : ℝ => heatAverage t f x) := by
  apply continuous_of_dominated (bound := fun _ : V => C)
  · intro t
    exact (hf.comp (by fun_prop)).aestronglyMeasurable
  · intro t
    exact Eventually.of_forall (fun z => hbound _)
  · exact integrable_const C
  · exact Eventually.of_forall (fun z => hf.comp (by fun_prop))

theorem heatAverage_zero [CompleteSpace F] (f : V → F) (x : V) :
    heatAverage 0 f x = f x := by
  simp [heatAverage]

theorem heatAverage_hasDerivAt_time_integral {f : V → F} {f' : V → V →L[ℝ] F}
    (hf : Continuous f) (hf' : Continuous f') (hderiv : ∀ x, HasFDerivAt f (f' x) x)
    {C D : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) (hdbound : ∀ x, ‖f' x‖ ≤ D)
    {t : ℝ} (ht : 0 < t) (x : V) :
    HasDerivAt (fun s => heatAverage s f x)
      ((Real.sqrt (2 * t))⁻¹ • ∫ z, f' (x + Real.sqrt (2 * t) • z) z ∂stdGaussian V) t := by
  have hD : 0 ≤ D := (norm_nonneg (f' 0)).trans (hdbound 0)
  have hroot : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs : Ioi (t / 2) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
  have hscale (s : ℝ) (hs' : s ∈ Ioi (t / 2)) :
      HasDerivAt (fun a : ℝ => Real.sqrt (2 * a)) (Real.sqrt (2 * s))⁻¹ s := by
    have hs1 : t / 2 < s := hs'
    have hs0 : 0 < 2 * s := by linarith
    convert! ((hasDerivAt_id s).const_mul 2).sqrt (by simpa using hs0.ne') using 1
    simp only [id_eq, mul_one]
    field_simp
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := stdGaussian V)
    (F := fun s z => f (x + Real.sqrt (2 * s) • z))
    (F' := fun s z => (Real.sqrt (2 * s))⁻¹ • f' (x + Real.sqrt (2 * s) • z) z)
    (bound := fun z => ((Real.sqrt t)⁻¹ * D) * ‖z‖) hs
    (Eventually.of_forall (fun s => (hf.comp (by fun_prop)).aestronglyMeasurable))
    (heatAverage_integrable_of_bound hf hbound t x)
    (((hf'.comp (by fun_prop)).clm_apply continuous_id).const_smul _).aestronglyMeasurable
    (Eventually.of_forall (fun z s hs' => by
      have hs1 : t / 2 < s := hs'
      have hs0 : 0 < Real.sqrt (2 * s) := Real.sqrt_pos.mpr (by linarith)
      have hrootle : Real.sqrt t ≤ Real.sqrt (2 * s) := Real.sqrt_le_sqrt (by linarith)
      have hinv : (Real.sqrt (2 * s))⁻¹ ≤ (Real.sqrt t)⁻¹ := inv_anti₀ hroot hrootle
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0)]
      calc
        _ ≤ (Real.sqrt (2 * s))⁻¹ * (D * ‖z‖) :=
          mul_le_mul_of_nonneg_left
            (((f' _).le_opNorm z).trans (mul_le_mul_of_nonneg_right (hdbound _) (norm_nonneg z)))
            (inv_nonneg.mpr hs0.le)
        _ ≤ (Real.sqrt t)⁻¹ * (D * ‖z‖) :=
          mul_le_mul_of_nonneg_right hinv (mul_nonneg hD (norm_nonneg z))
        _ = _ := by ring))
    (IsGaussian.integrable_id.norm.const_mul ((Real.sqrt t)⁻¹ * D))
    (Eventually.of_forall (fun z s hs' => by
      simpa only [Function.comp_def, map_smul] using
        (hderiv _).comp_hasDerivAt s (((hscale s hs').smul_const z).const_add x)))
  simpa only [heatAverage, integral_smul] using h.2

end PoincareConjecture.M35.RadialGauge
