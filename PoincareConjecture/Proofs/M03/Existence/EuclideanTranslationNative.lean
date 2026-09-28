import PoincareConjecture.Proofs.M03.Existence.SpectralSmallTimeNative
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace PoincareConjecture.EuclideanTranslationNative

open SpectralHeatNative (timeMeasure)

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

abbrev ScalarL2 (n : ℕ) := Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))

def translateLp (h : E) (F : ScalarL2 n) : ScalarL2 n :=
  Lp.compMeasurePreserving (fun x => x + h) (measurePreserving_add_right volume h) F

theorem translateLp_ae_eq (h : E) (F : ScalarL2 n) :
    translateLp h F =ᵐ[volume] (fun x => F (x + h)) :=
  Lp.coeFn_compMeasurePreserving F (measurePreserving_add_right volume h)

theorem norm_translateLp (h : E) (F : ScalarL2 n) : ‖translateLp h F‖ = ‖F‖ :=
  Lp.norm_compMeasurePreserving F (measurePreserving_add_right volume h)

theorem scalarLp_norm_sq (F : ScalarL2 n) : ‖F‖ ^ 2 = ∫ x, (F x) ^ 2 := by
  calc
    ‖F‖ ^ 2 = inner ℝ F F := (real_inner_self_eq_norm_sq F).symm
    _ = ∫ x, inner ℝ (F x) (F x) := L2.inner_def F F
    _ = _ := by simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem scalar_toLp_norm_sq {f : E → ℝ} (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 := by
  rw [scalarLp_norm_sq]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

theorem hasDerivAt_segment (x h : E) (s : ℝ) :
    HasDerivAt (fun t : ℝ => x + t • h) h s := by
  convert! (hasDerivAt_const s x).add ((hasDerivAt_id s).smul_const h) using 1 <;>
    first | rfl | simp only [one_smul, zero_add, Pi.add_apply, id_eq]

theorem continuous_segment_derivative {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (x h : E) : Continuous (fun s : ℝ => fderiv ℝ f (x + s • h) h) :=
  ((hf.continuous_fderiv one_ne_zero).comp
    (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const

theorem translation_eq_integral_derivative {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (x h : E) :
    f (x + h) - f x = ∫ s in (0 : ℝ)..1, fderiv ℝ f (x + s • h) h := by
  have hd (s : ℝ) : HasDerivAt (fun t : ℝ => f (x + t • h))
      (fderiv ℝ f (x + s • h) h) s :=
    (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_segment x h s)
  have hi : IntervalIntegrable (fun s : ℝ => fderiv ℝ f (x + s • h) h) volume 0 1 :=
    (continuous_segment_derivative hf x h).intervalIntegrable 0 1
  simpa only [zero_smul, add_zero, one_smul] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi).symm

theorem translation_sq_le_integral_derivative_sq {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (x h : E) :
    (f (x + h) - f x) ^ 2 ≤
      ∫ s in (0 : ℝ)..1, (fderiv ℝ f (x + s • h) h) ^ 2 := by
  rw [translation_eq_integral_derivative hf x h]
  have hc := continuous_segment_derivative hf x h
  simpa only [one_mul] using
    SpectralHeatNative.integral_sq_le_time_mul_integral_sq
      (by norm_num : (0 : ℝ) ≤ 1) (hc.intervalIntegrable 0 1)
      ((hc.pow 2).intervalIntegrable 0 1)

theorem integrable_segment_derivative_sq {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (h : E) (hD : MemLp (fun x => fderiv ℝ f x h) 2 volume) :
    Integrable (fun p : ℝ × E => (fderiv ℝ f (p.2 + p.1 • h) h) ^ 2)
      ((timeMeasure 1).prod volume) := by
  have hc : Continuous (fun p : ℝ × E => (fderiv ℝ f (p.2 + p.1 • h) h) ^ 2) :=
    (((hf.continuous_fderiv one_ne_zero).comp
      (continuous_snd.add (continuous_fst.smul continuous_const))).clm_apply
        continuous_const).pow 2
  apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall (fun s => hD.integrable_sq.comp_add_right (s • h))
  · have heq : (fun s : ℝ => ∫ x, ‖(fderiv ℝ f (x + s • h) h) ^ 2‖) =
        (fun _ : ℝ => ∫ x, (fderiv ℝ f x h) ^ 2) := by
      funext s
      simp only [Real.norm_eq_abs, abs_pow, sq_abs]
      exact integral_add_right_eq_self (fun x => (fderiv ℝ f x h) ^ 2) (s • h)
    rw [heq]
    exact integrable_const _

theorem integral_translation_sq_le_directional {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfL2 : MemLp f 2 volume)
    (h : E) (hD : MemLp (fun x => fderiv ℝ f x h) 2 volume) :
    (∫ x, (f (x + h) - f x) ^ 2) ≤ ∫ x, (fderiv ℝ f x h) ^ 2 := by
  have hi := integrable_segment_derivative_sq hf h hD
  have htrans := hfL2.comp_measurePreserving (measurePreserving_add_right volume h)
  calc
    _ ≤ ∫ x, ∫ s, (fderiv ℝ f (x + s • h) h) ^ 2 ∂timeMeasure 1 := by
      apply integral_mono (htrans.sub hfL2).integrable_sq hi.integral_prod_right
      intro x
      simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        timeMeasure, Pi.sub_apply, Function.comp_apply] using
        translation_sq_le_integral_derivative_sq hf x h
    _ = ∫ s, ∫ x, (fderiv ℝ f (x + s • h) h) ^ 2 ∂volume ∂timeMeasure 1 :=
      (integral_integral_swap hi).symm
    _ = ∫ s, (∫ x, (fderiv ℝ f x h) ^ 2) ∂timeMeasure 1 := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun s =>
        integral_add_right_eq_self (fun x => (fderiv ℝ f x h) ^ 2) (s • h))
    _ = _ := by
      simp [timeMeasure, integral_const, Measure.real, Real.volume_Ioc]

theorem translateLp_sub_norm_sq_le_directional {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfL2 : MemLp f 2 volume)
    (h : E) (hD : MemLp (fun x => fderiv ℝ f x h) 2 volume) :
    ‖translateLp h (hfL2.toLp f) - hfL2.toLp f‖ ^ 2 ≤
      ∫ x, (fderiv ℝ f x h) ^ 2 := by
  unfold translateLp
  rw [Lp.toLp_compMeasurePreserving, ← MemLp.toLp_sub, scalar_toLp_norm_sq]
  exact integral_translation_sq_le_directional hf hfL2 h hD

theorem linearFunctional_eq_sum (L : E →L[ℝ] ℝ) (h : E) :
    L h = ∑ i, h i * L (EuclideanSpace.single i 1) := by
  have hb := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr h
  have heq := congrArg L hb
  simpa only [map_sum, map_smul, smul_eq_mul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply] using heq.symm

theorem linearFunctional_sq_le (L : E →L[ℝ] ℝ) (h : E) :
    (L h) ^ 2 ≤ ‖h‖ ^ 2 * ∑ i, (L (EuclideanSpace.single i 1)) ^ 2 := by
  rw [linearFunctional_eq_sum L h]
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => h i) (fun i => L (EuclideanSpace.single i 1))
  have hn : ∑ i, (h i) ^ 2 = ‖h‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) h).symm
  simpa only [hn] using hs

theorem memLp_directional_of_coordinates {f : E → ℝ}
    (hcoord : ∀ i : Fin n,
      MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 volume) (h : E) :
    MemLp (fun x => fderiv ℝ f x h) 2 volume := by
  have hs : MemLp
      (fun x => ∑ i, h i * fderiv ℝ f x (EuclideanSpace.single i 1)) 2 volume :=
    memLp_finsetSum Finset.univ (fun i _ => (hcoord i).const_mul (h i))
  have heq : (fun x => fderiv ℝ f x h) =
      (fun x => ∑ i, h i * fderiv ℝ f x (EuclideanSpace.single i 1)) :=
    funext (fun x => linearFunctional_eq_sum (fderiv ℝ f x) h)
  rw [heq]
  exact hs

theorem integral_directional_sq_le_coordinates {f : E → ℝ}
    (hcoord : ∀ i : Fin n,
      MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 volume) (h : E) :
    (∫ x, (fderiv ℝ f x h) ^ 2) ≤
      ‖h‖ ^ 2 * ∑ i, ∫ x, (fderiv ℝ f x (EuclideanSpace.single i 1)) ^ 2 := by
  have hsum : Integrable
      (fun x => ∑ i, (fderiv ℝ f x (EuclideanSpace.single i 1)) ^ 2) volume :=
    integrable_finsetSum Finset.univ (fun i _ => (hcoord i).integrable_sq)
  calc
    _ ≤ ∫ x, ‖h‖ ^ 2 * ∑ i, (fderiv ℝ f x (EuclideanSpace.single i 1)) ^ 2 :=
      integral_mono (memLp_directional_of_coordinates hcoord h).integrable_sq
        (hsum.const_mul _) (fun x => linearFunctional_sq_le (fderiv ℝ f x) h)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum Finset.univ
        (fun i _ => (hcoord i).integrable_sq)]

theorem translateLp_sub_norm_sq_le_coordinates {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfL2 : MemLp f 2 volume)
    (hcoord : ∀ i : Fin n,
      MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 volume) (h : E) :
    ‖translateLp h (hfL2.toLp f) - hfL2.toLp f‖ ^ 2 ≤
      ‖h‖ ^ 2 * ∑ i, ∫ x, (fderiv ℝ f x (EuclideanSpace.single i 1)) ^ 2 :=
  (translateLp_sub_norm_sq_le_directional hf hfL2 h
    (memLp_directional_of_coordinates hcoord h)).trans
      (integral_directional_sq_le_coordinates hcoord h)

end PoincareConjecture.EuclideanTranslationNative
