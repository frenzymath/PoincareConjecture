/-
Provenance and modification notice (recorded 2026-09-29).
Notices for the adapted portions:
Copyright 2026 The DifferentialGeometry contributors
Source: https://github.com/qinz1yang/differential-geometry
DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatKernelSup.lean
Comparison revision: 1b535dd102b94cc42b107cca27059687888f08b3.
Modifications: Imports, module paths, and namespaces were adapted to this PoincareConjecture
development.
License: Apache-2.0; see LICENSES/Apache-2.0.txt and NOTICE.
See MODIFICATIONS.md for the reviewed file mapping and scope of this notice.
-/

import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Kernel.Gaussian
import Mathlib.Topology.ContinuousMap.Bounded.Normed

noncomputable section

open MeasureTheory Real
open scoped RealInnerProductSpace

namespace Poincare.Parabolic.Interior.Kernel

section SupKernel

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def supKernel (η : V → ℝ) (u : BoundedContinuousFunction V F) (x : V) : F :=
  ∫ y, η y • u (x - y)

omit [CompleteSpace F] in
theorem supKernel_int {η : V → ℝ} (hη : Integrable η)
    (u : BoundedContinuousFunction V F) (x : V) :
    Integrable (fun y : V => η y • u (x - y)) := by
  refine (hη.norm.mul_const ‖u‖).mono' ?_ ?_
  · exact hη.aestronglyMeasurable.smul
      ((u.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · filter_upwards with y
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm (x - y)) (norm_nonneg _)

omit [CompleteSpace F] in
theorem supKernel_norm {η : V → ℝ} (hη : Integrable η)
    (u : BoundedContinuousFunction V F) (x : V) :
    ‖supKernel η u x‖ ≤ (∫ y, ‖η y‖) * ‖u‖ := by
  unfold supKernel
  calc
    ‖∫ y, η y • u (x - y)‖
        ≤ ∫ y, ‖η y‖ * ‖u‖ :=
      norm_integral_le_of_norm_le (hη.norm.mul_const ‖u‖)
        (Filter.Eventually.of_forall fun y => by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm (x - y))
            (norm_nonneg _))
    _ = (∫ y, ‖η y‖) * ‖u‖ := by rw [integral_mul_const]

omit [CompleteSpace F] in
theorem supKernel_sub {η : V → ℝ} (hη : Integrable η)
    (u v : BoundedContinuousFunction V F) (x : V) :
    supKernel η (u - v) x = supKernel η u x - supKernel η v x := by
  unfold supKernel
  rw [← integral_sub (supKernel_int hη u x) (supKernel_int hη v x)]
  apply integral_congr_ae
  filter_upwards with y
  simp only [BoundedContinuousFunction.sub_apply, smul_sub]

omit [CompleteSpace F] in
theorem supKernel_contract {η : V → ℝ} (hη : Integrable η)
    (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∫ y, η y = 1)
    (u : BoundedContinuousFunction V F) (x : V) :
    ‖supKernel η u x‖ ≤ ‖u‖ := by
  refine (supKernel_norm hη u x).trans_eq ?_
  have habs : (fun y : V => ‖η y‖) = η := by
    funext y
    simp [Real.norm_eq_abs, abs_of_nonneg (hη0 y)]
  rw [habs, hη1, one_mul]

end SupKernel

section HeatSup

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def heatSup (t : ℝ) (u : BoundedContinuousFunction V F) (x : V) : F :=
  supKernel (heatKernel t) u x

omit [CompleteSpace F] in
theorem heatSup_contract {t : ℝ} (ht : 0 < t)
    (u : BoundedContinuousFunction V F) (x : V) :
    ‖heatSup t u x‖ ≤ ‖u‖ := by
  exact supKernel_contract (heatKernel_int ht) (heatKernel_nonneg ht)
    (integral_heatKernel ht) u x

def heatD1Sup (t : ℝ) (v : V) (u : BoundedContinuousFunction V F) (x : V) : F :=
  supKernel (heatD1 t v) u x

def heatD2Sup (t : ℝ) (v w : V) (u : BoundedContinuousFunction V F) (x : V) : F :=
  supKernel (heatD2 t v w) u x

omit [CompleteSpace F] in
theorem heatD1Sup_sub {t : ℝ} (ht : 0 < t) (v : V)
    (u₁ u₂ : BoundedContinuousFunction V F) (x : V) :
    heatD1Sup t v (u₁ - u₂) x =
      heatD1Sup t v u₁ x - heatD1Sup t v u₂ x := by
  exact supKernel_sub (heatD1_int ht v) u₁ u₂ x

omit [CompleteSpace F] in
theorem heatD2Sup_sub {t : ℝ} (ht : 0 < t) (v w : V)
    (u₁ u₂ : BoundedContinuousFunction V F) (x : V) :
    heatD2Sup t v w (u₁ - u₂) x =
      heatD2Sup t v w u₁ x - heatD2Sup t v w u₂ x := by
  exact supKernel_sub (heatD2_int ht v w) u₁ u₂ x

omit [CompleteSpace F] in
theorem heatD1Sup_norm {t : ℝ} (ht : 0 < t) (v : V)
    (u : BoundedContinuousFunction V F) (x : V) :
    ‖heatD1Sup t v u x‖ ≤
      (‖v‖ * (heatScale t)⁻¹ * heatC1 V) * ‖u‖ := by
  refine (supKernel_norm (heatD1_int ht v) u x).trans ?_
  exact mul_le_mul_of_nonneg_right (integral_norm_D1 ht v) (norm_nonneg _)

omit [CompleteSpace F] in
theorem heatD2Sup_norm {t : ℝ} (ht : 0 < t) (v w : V)
    (u : BoundedContinuousFunction V F) (x : V) :
    ‖heatD2Sup t v w u x‖ ≤
      (‖v‖ * ‖w‖ * t⁻¹ * heatC2 V) * ‖u‖ := by
  refine (supKernel_norm (heatD2_int ht v w) u x).trans ?_
  exact mul_le_mul_of_nonneg_right (integral_norm_D2 ht v w) (norm_nonneg _)

end HeatSup

end Poincare.Parabolic.Interior.Kernel

end
