import PoincareConjecture.Proofs.M03.Existence.SpectralSmallTimeNative
import PoincareConjecture.Proofs.M03.Existence.SpectralLpOperatorNative
import Mathlib.Topology.ContinuousMap.Compact










set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set

namespace PoincareConjecture.SpectralHeatNative

variable {iota : Type*} [Countable iota] {T : ℝ}

abbrev ResponsePath (iota : Type*) (T : ℝ) := C(Icc (0 : ℝ) T, State iota)

def responsePath (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) : ResponsePath iota T where
  toFun t := responseState lambda F t
  continuous_toFun := (continuousOn_responseState_of_memLp hT (Lp.memLp F) lambda).domRestrict

def tracePath (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) : ResponsePath iota T where
  toFun t := SpectralTraceNative.traceState lambda F t
  continuous_toFun :=
    (SpectralTraceNative.continuousOn_traceState hT (Lp.memLp F) lambda).domRestrict

@[simp] theorem responsePath_apply (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) (t : Icc (0 : ℝ) T) :
    responsePath hT lambda F t = responseState lambda F t := rfl

theorem tracePath_apply_coordinate (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) (t : Icc (0 : ℝ) T) (i : iota) :
    tracePath hT lambda F t i = Real.sqrt (lambda i) * responsePath hT lambda F t i := by
  change SpectralTraceNative.traceState lambda F t i =
    Real.sqrt (lambda i) * responseState lambda F t i
  rw [SpectralTraceNative.traceState_apply (Lp.memLp F) lambda t.property,
    responseState_apply_of_memLp (Lp.memLp F) lambda t.property]
  rfl

theorem responsePath_add (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F G : ForcingSpace iota T) :
    responsePath hT lambda (F + G) = responsePath hT lambda F + responsePath hT lambda G := by
  apply ContinuousMap.ext
  intro t
  change responseState lambda (F + G : ForcingSpace iota T) t =
    responseState lambda F t + responseState lambda G t
  calc
    _ = responseState lambda (fun s => F s + G s) t :=
      responseState_eq_of_ae_eq (Lp.memLp (F + G)) ((Lp.memLp F).add (Lp.memLp G))
        lambda (Lp.coeFn_add F G) t.property
    _ = _ := responseState_add_of_memLp (Lp.memLp F) (Lp.memLp G) lambda t.property

theorem responsePath_smul (hT : 0 ≤ T) (lambda : iota → NNReal)
    (a : ℝ) (F : ForcingSpace iota T) :
    responsePath hT lambda (a • F) = a • responsePath hT lambda F := by
  apply ContinuousMap.ext
  intro t
  change responseState lambda (a • F : ForcingSpace iota T) t = a • responseState lambda F t
  calc
    _ = responseState lambda (fun s => a • F s) t :=
      responseState_eq_of_ae_eq (Lp.memLp (a • F)) ((Lp.memLp F).const_smul a)
        lambda (Lp.coeFn_smul a F) t.property
    _ = _ := responseState_smul_of_memLp (Lp.memLp F) lambda a t.property

theorem tracePath_add (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F G : ForcingSpace iota T) :
    tracePath hT lambda (F + G) = tracePath hT lambda F + tracePath hT lambda G := by
  apply ContinuousMap.ext
  intro t
  apply lp.ext
  funext i
  change tracePath hT lambda (F + G) t i =
    tracePath hT lambda F t i + tracePath hT lambda G t i
  rw [tracePath_apply_coordinate, tracePath_apply_coordinate, tracePath_apply_coordinate,
    responsePath_add]
  change Real.sqrt (lambda i) * (responsePath hT lambda F t i + responsePath hT lambda G t i) = _
  ring

theorem tracePath_smul (hT : 0 ≤ T) (lambda : iota → NNReal)
    (a : ℝ) (F : ForcingSpace iota T) :
    tracePath hT lambda (a • F) = a • tracePath hT lambda F := by
  apply ContinuousMap.ext
  intro t
  apply lp.ext
  funext i
  change tracePath hT lambda (a • F) t i = a * tracePath hT lambda F t i
  rw [tracePath_apply_coordinate, tracePath_apply_coordinate, responsePath_smul]
  change Real.sqrt (lambda i) * (a * responsePath hT lambda F t i) = _
  ring

theorem norm_responsePath_le (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) : ‖responsePath hT lambda F‖ ≤ Real.sqrt T * ‖F‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr
  intro t
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  calc
    _ ≤ t.val * ∫ s, ‖F s‖ ^ 2 ∂timeMeasure T :=
      norm_responseState_sq_le_time_energy (Lp.memLp F) lambda t.property
    _ ≤ T * ‖F‖ ^ 2 := by
      rw [← forcing_norm_sq]
      exact mul_le_mul_of_nonneg_right t.property.2 (sq_nonneg _)
    _ = _ := by rw [mul_pow, Real.sq_sqrt hT]

theorem norm_tracePath_le (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) : ‖tracePath hT lambda F‖ ≤ ‖F‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [forcing_norm_sq]
  exact SpectralTraceNative.norm_traceState_sq_le (Lp.memLp F) lambda t.property

def responsePathLinearMap (hT : 0 ≤ T) (lambda : iota → NNReal) :
    ForcingSpace iota T →ₗ[ℝ] ResponsePath iota T where
  toFun := responsePath hT lambda
  map_add' := responsePath_add hT lambda
  map_smul' := responsePath_smul hT lambda

def tracePathLinearMap (hT : 0 ≤ T) (lambda : iota → NNReal) :
    ForcingSpace iota T →ₗ[ℝ] ResponsePath iota T where
  toFun := tracePath hT lambda
  map_add' := tracePath_add hT lambda
  map_smul' := tracePath_smul hT lambda

def responseOperator (hT : 0 ≤ T) (lambda : iota → NNReal) :
    ForcingSpace iota T →L[ℝ] ResponsePath iota T :=
  (responsePathLinearMap hT lambda).mkContinuous (Real.sqrt T)
    (fun F => by
      change ‖responsePath hT lambda F‖ ≤ Real.sqrt T * ‖F‖
      exact norm_responsePath_le hT lambda F)

def traceOperator (hT : 0 ≤ T) (lambda : iota → NNReal) :
    ForcingSpace iota T →L[ℝ] ResponsePath iota T :=
  (tracePathLinearMap hT lambda).mkContinuous 1
    (fun F => by
      change ‖tracePath hT lambda F‖ ≤ 1 * ‖F‖
      simpa only [one_mul] using norm_tracePath_le hT lambda F)

@[simp] theorem responseOperator_apply (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) : responseOperator hT lambda F = responsePath hT lambda F := rfl

@[simp] theorem traceOperator_apply (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) : traceOperator hT lambda F = tracePath hT lambda F := rfl

theorem norm_responseOperator_le (hT : 0 ≤ T) (lambda : iota → NNReal) :
    ‖responseOperator hT lambda‖ ≤ Real.sqrt T := by
  exact (responsePathLinearMap hT lambda).mkContinuous_norm_le (Real.sqrt_nonneg _) _

theorem norm_traceOperator_le (hT : 0 ≤ T) (lambda : iota → NNReal) :
    ‖traceOperator hT lambda‖ ≤ 1 := by
  exact (tracePathLinearMap hT lambda).mkContinuous_norm_le (by norm_num) _

end PoincareConjecture.SpectralHeatNative
