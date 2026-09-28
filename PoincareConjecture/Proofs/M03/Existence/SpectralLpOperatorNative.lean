import PoincareConjecture.Proofs.M03.Existence.SpectralResponseLinearityNative
import Mathlib.Analysis.InnerProductSpace.l2Space









set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PoincareConjecture.SpectralHeatNative

variable {iota : Type*}

abbrev ForcingSpace (iota : Type*) (T : ℝ) := Lp (State iota) 2 (timeMeasure T)


theorem forcing_norm_sq {μ : Measure ℝ} (F : Lp (State iota) 2 μ) :
    ‖F‖ ^ 2 = ∫ t, ‖F t‖ ^ 2 ∂μ := by
  calc
    ‖F‖ ^ 2 = inner ℝ F F := (real_inner_self_eq_norm_sq F).symm
    _ = ∫ t, inner ℝ (F t) (F t) ∂μ := L2.inner_def F F
    _ = _ := by simp only [real_inner_self_eq_norm_sq]

theorem norm_toLp_sq {μ : Measure ℝ} {f : ℝ → State iota} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂μ := by
  rw [forcing_norm_sq]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with t ht
  rw [ht]

variable [Countable iota] {T : ℝ}

def derivativeLp (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) : ForcingSpace iota T :=
  (memLp_derivativeState_of_memLp hT (Lp.memLp F) lambda).toLp (derivativeState lambda F)

def generatorLp (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) : ForcingSpace iota T :=
  (memLp_generatorState_of_memLp hT (Lp.memLp F) lambda).toLp (generatorState lambda F)

theorem derivativeLp_add (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F G : ForcingSpace iota T) :
    derivativeLp hT lambda (F + G) = derivativeLp hT lambda F + derivativeLp hT lambda G := by
  unfold derivativeLp
  rw [← MemLp.toLp_add]
  apply MemLp.toLp_congr
  exact (ae_derivativeState_eq_of_ae_eq hT (Lp.memLp (F + G))
    ((Lp.memLp F).add (Lp.memLp G)) lambda (Lp.coeFn_add F G)).trans
      (ae_derivativeState_add_of_memLp hT (Lp.memLp F) (Lp.memLp G) lambda)

theorem generatorLp_add (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F G : ForcingSpace iota T) :
    generatorLp hT lambda (F + G) = generatorLp hT lambda F + generatorLp hT lambda G := by
  unfold generatorLp
  rw [← MemLp.toLp_add]
  apply MemLp.toLp_congr
  exact (ae_generatorState_eq_of_ae_eq hT (Lp.memLp (F + G))
    ((Lp.memLp F).add (Lp.memLp G)) lambda (Lp.coeFn_add F G)).trans
      (ae_generatorState_add_of_memLp hT (Lp.memLp F) (Lp.memLp G) lambda)

theorem derivativeLp_smul (hT : 0 ≤ T) (lambda : iota → NNReal)
    (a : ℝ) (F : ForcingSpace iota T) :
    derivativeLp hT lambda (a • F) = a • derivativeLp hT lambda F := by
  unfold derivativeLp
  rw [← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  exact (ae_derivativeState_eq_of_ae_eq hT (Lp.memLp (a • F))
    ((Lp.memLp F).const_smul a) lambda (Lp.coeFn_smul a F)).trans
      (ae_derivativeState_smul_of_memLp hT (Lp.memLp F) lambda a)

theorem generatorLp_smul (hT : 0 ≤ T) (lambda : iota → NNReal)
    (a : ℝ) (F : ForcingSpace iota T) :
    generatorLp hT lambda (a • F) = a • generatorLp hT lambda F := by
  unfold generatorLp
  rw [← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  exact (ae_generatorState_eq_of_ae_eq hT (Lp.memLp (a • F))
    ((Lp.memLp F).const_smul a) lambda (Lp.coeFn_smul a F)).trans
      (ae_generatorState_smul_of_memLp hT (Lp.memLp F) lambda a)


theorem derivativeLp_generatorLp_energy (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) :
    ‖derivativeLp hT lambda F‖ ^ 2 + ‖generatorLp hT lambda F‖ ^ 2 ≤ ‖F‖ ^ 2 := by
  unfold derivativeLp generatorLp
  rw [norm_toLp_sq, norm_toLp_sq, forcing_norm_sq]
  exact integral_response_energy_le_of_memLp hT (Lp.memLp F) lambda

theorem norm_derivativeLp_le (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) : ‖derivativeLp hT lambda F‖ ≤ ‖F‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have he := derivativeLp_generatorLp_energy hT lambda F
  have hG := sq_nonneg ‖generatorLp hT lambda F‖
  linarith

theorem norm_generatorLp_le (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) : ‖generatorLp hT lambda F‖ ≤ ‖F‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have he := derivativeLp_generatorLp_energy hT lambda F
  have hD := sq_nonneg ‖derivativeLp hT lambda F‖
  linarith

def derivativeLinearMap (hT : 0 ≤ T) (lambda : iota → NNReal) :
    ForcingSpace iota T →ₗ[ℝ] ForcingSpace iota T where
  toFun := derivativeLp hT lambda
  map_add' := derivativeLp_add hT lambda
  map_smul' := derivativeLp_smul hT lambda

def generatorLinearMap (hT : 0 ≤ T) (lambda : iota → NNReal) :
    ForcingSpace iota T →ₗ[ℝ] ForcingSpace iota T where
  toFun := generatorLp hT lambda
  map_add' := generatorLp_add hT lambda
  map_smul' := generatorLp_smul hT lambda


def derivativeOperator (hT : 0 ≤ T) (lambda : iota → NNReal) :
    ForcingSpace iota T →L[ℝ] ForcingSpace iota T :=
  (derivativeLinearMap hT lambda).mkContinuous 1
    (fun F => by
      change ‖derivativeLp hT lambda F‖ ≤ 1 * ‖F‖
      simpa only [one_mul] using norm_derivativeLp_le hT lambda F)


def generatorOperator (hT : 0 ≤ T) (lambda : iota → NNReal) :
    ForcingSpace iota T →L[ℝ] ForcingSpace iota T :=
  (generatorLinearMap hT lambda).mkContinuous 1
    (fun F => by
      change ‖generatorLp hT lambda F‖ ≤ 1 * ‖F‖
      simpa only [one_mul] using norm_generatorLp_le hT lambda F)

@[simp] theorem derivativeOperator_apply (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) : derivativeOperator hT lambda F = derivativeLp hT lambda F := rfl

@[simp] theorem generatorOperator_apply (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) : generatorOperator hT lambda F = generatorLp hT lambda F := rfl

theorem norm_derivativeOperator_le (hT : 0 ≤ T) (lambda : iota → NNReal) :
    ‖derivativeOperator hT lambda‖ ≤ 1 := by
  exact (derivativeLinearMap hT lambda).mkContinuous_norm_le (by norm_num) _

theorem norm_generatorOperator_le (hT : 0 ≤ T) (lambda : iota → NNReal) :
    ‖generatorOperator hT lambda‖ ≤ 1 := by
  exact (generatorLinearMap hT lambda).mkContinuous_norm_le (by norm_num) _

theorem derivativeLp_add_generatorLp (hT : 0 ≤ T) (lambda : iota → NNReal)
    (F : ForcingSpace iota T) : derivativeLp hT lambda F + generatorLp hT lambda F = F := by
  have hD := memLp_derivativeState_of_memLp hT (Lp.memLp F) lambda
  have hG := memLp_generatorState_of_memLp hT (Lp.memLp F) lambda
  calc
    _ = (hD.add hG).toLp (derivativeState lambda F + generatorState lambda F) :=
      (hD.toLp_add hG).symm
    _ = (Lp.memLp F).toLp F := by
      apply MemLp.toLp_congr
      exact derivativeState_add_generatorState_of_memLp hT (Lp.memLp F) lambda
    _ = F := Lp.toLp_coeFn F (Lp.memLp F)


theorem derivativeOperator_add_generatorOperator (hT : 0 ≤ T) (lambda : iota → NNReal) :
    derivativeOperator hT lambda + generatorOperator hT lambda =
      ContinuousLinearMap.id ℝ (ForcingSpace iota T) := by
  apply ContinuousLinearMap.ext
  intro F
  exact derivativeLp_add_generatorLp hT lambda F

end PoincareConjecture.SpectralHeatNative
