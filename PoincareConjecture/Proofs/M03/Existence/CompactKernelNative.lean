import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli









set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

namespace PoincareConjecture.CompactKernelNative

variable {X H : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def kernelFunction (k : C(X, H)) (u : H) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => inner ℝ (k x) u, k.continuous.inner continuous_const⟩

@[simp] theorem kernelFunction_apply (k : C(X, H)) (u : H) (x : X) :
    kernelFunction k u x = inner ℝ (k x) u := rfl

theorem norm_kernelFunction_le (k : C(X, H)) (u : H) :
    ‖kernelFunction k u‖ ≤ ‖k‖ * ‖u‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro x
  exact (norm_inner_le_norm (k x) u).trans
    (mul_le_mul_of_nonneg_right (k.norm_coe_le_norm x) (norm_nonneg u))

def kernelLinearMap (k : C(X, H)) : H →ₗ[ℝ] (X →ᵇ ℝ) where
  toFun := kernelFunction k
  map_add' u v := by
    apply BoundedContinuousFunction.ext
    intro x
    exact inner_add_right (k x) u v
  map_smul' a u := by
    apply BoundedContinuousFunction.ext
    intro x
    exact inner_smul_right (k x) u a

def kernelOperator (k : C(X, H)) : H →L[ℝ] (X →ᵇ ℝ) :=
  (kernelLinearMap k).mkContinuous ‖k‖ (fun u => by
    change ‖kernelFunction k u‖ ≤ ‖k‖ * ‖u‖
    exact norm_kernelFunction_le k u)

@[simp] theorem kernelOperator_apply (k : C(X, H)) (u : H) :
    kernelOperator k u = kernelFunction k u := rfl

theorem norm_kernelOperator_le (k : C(X, H)) : ‖kernelOperator k‖ ≤ ‖k‖ :=
  (kernelLinearMap k).mkContinuous_norm_le (norm_nonneg _) _

theorem kernelFunction_dist_le (k : C(X, H)) (u : H) (x y : X) :
    dist (kernelFunction k u x) (kernelFunction k u y) ≤ ‖k x - k y‖ * ‖u‖ := by
  rw [dist_eq_norm, kernelFunction_apply, kernelFunction_apply, ← inner_sub_left]
  exact norm_inner_le_norm _ _

theorem equicontinuous_kernel_unitBall (k : C(X, H)) :
    Equicontinuous ((↑) : (kernelFunction k '' Metric.closedBall (0 : H) 1) → X → ℝ) := by
  intro x
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hk : Tendsto (fun y => ‖k x - k y‖) (𝓝 x) (𝓝 (0 : ℝ)) := by
    have hc : ContinuousAt (fun y => ‖k x - k y‖) x :=
      (continuous_const.sub k.continuous).norm.continuousAt
    simpa only [sub_self, norm_zero] using
      hc.tendsto
  filter_upwards [hk.eventually (gt_mem_nhds hε)] with y hy
  rintro ⟨f, u, hu, rfl⟩
  have hun : ‖u‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hu
  exact ((kernelFunction_dist_le k u x y).trans
    (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hun (norm_nonneg (k x - k y)))).trans_lt hy


theorem isCompact_closure_kernel_unitBall (k : C(X, H)) :
    IsCompact (closure (kernelFunction k '' Metric.closedBall (0 : H) 1)) := by
  apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℝ) ‖k‖)
    (isCompact_closedBall _ _) _ _ (equicontinuous_kernel_unitBall k)
  intro f x hf
  obtain ⟨u, hu, rfl⟩ := hf
  rw [Metric.mem_closedBall, dist_zero_right]
  have hun : ‖u‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hu
  calc
    ‖kernelFunction k u x‖ ≤ ‖kernelFunction k u‖ :=
      (kernelFunction k u).norm_coe_le_norm x
    _ ≤ ‖k‖ * ‖u‖ := norm_kernelFunction_le k u
    _ ≤ ‖k‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hun (norm_nonneg k)


theorem isCompactOperator_kernelOperator (k : C(X, H)) :
    IsCompactOperator (kernelOperator k) := by
  apply (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image
    (kernelOperator k)).mpr
  exact ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ (by norm_num),
    isCompact_closure_kernel_unitBall k⟩

variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]


def kernelLpOperator (k : C(X, H)) : H →L[ℝ] Lp ℝ 2 μ :=
  (BoundedContinuousFunction.toLp 2 μ ℝ).comp (kernelOperator k)

theorem kernelLpOperator_ae_eq (k : C(X, H)) (u : H) :
    kernelLpOperator μ k u =ᵐ[μ] (fun x => inner ℝ (k x) u) :=
  BoundedContinuousFunction.coeFn_toLp 2 μ ℝ (kernelFunction k u)

theorem isCompactOperator_kernelLpOperator (k : C(X, H)) :
    IsCompactOperator (kernelLpOperator μ k) :=
  (isCompactOperator_kernelOperator k).clm_comp (BoundedContinuousFunction.toLp 2 μ ℝ)

end PoincareConjecture.CompactKernelNative
