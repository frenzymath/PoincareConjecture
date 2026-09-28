import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped ContDiff Topology
open Set Filter

namespace PoincareConjecture.Proofs.M09

universe u v

variable {K : Type v} [TopologicalSpace K] [CompactSpace K]
  {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def pointwiseLinear (A : C(K, E →L[ℝ] F)) : C(K, E) →L[ℝ] C(K, F) :=
  ({
    toFun := fun v ↦ ⟨fun k ↦ A k (v k), A.continuous.clm_apply v.continuous⟩
    map_add' := by intro v w; ext k; simp
    map_smul' := by intro c v; ext k; simp
  } : C(K, E) →ₗ[ℝ] C(K, F)).mkContinuous ‖A‖ (by
    intro v
    apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg v))).2
    intro k
    exact ((A k).le_opNorm (v k)).trans
      (mul_le_mul (A.norm_coe_le_norm k) (v.norm_coe_le_norm k)
        (norm_nonneg _) (norm_nonneg _)))

@[simp] theorem pointwiseLinear_apply (A : C(K, E →L[ℝ] F)) (v : C(K, E)) (k : K) :
    pointwiseLinear A v k = A k (v k) := rfl

theorem pointwiseLinear_norm_le (A : C(K, E →L[ℝ] F)) :
    ‖pointwiseLinear A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro v
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg v))).2
  intro k
  exact ((A k).le_opNorm (v k)).trans
    (mul_le_mul (A.norm_coe_le_norm k) (v.norm_coe_le_norm k)
      (norm_nonneg _) (norm_nonneg _))

noncomputable def pointwiseOperator : C(K, E →L[ℝ] F) →L[ℝ] (C(K, E) →L[ℝ] C(K, F)) := by
  let L : C(K, E →L[ℝ] F) →ₗ[ℝ] (C(K, E) →L[ℝ] C(K, F)) := {
    toFun := fun A ↦ pointwiseLinear (K := K) (E := E) (F := F) A
    map_add' := by intro A B; ext v k; rfl
    map_smul' := by intro c A; ext v k; rfl
  }
  have hL : ∀ A : C(K, E →L[ℝ] F), ‖L A‖ ≤ 1 * ‖A‖ := by
    intro (A : C(K, E →L[ℝ] F))
    change ‖pointwiseLinear (K := K) (E := E) (F := F) A‖ ≤ 1 * ‖A‖
    exact (pointwiseLinear_norm_le (K := K) (E := E) (F := F) A).trans_eq
      (one_mul ‖A‖).symm
  exact LinearMap.mkContinuous L 1 hL

@[simp] theorem pointwiseOperator_apply (A : C(K, E →L[ℝ] F)) :
    pointwiseOperator A = pointwiseLinear A := rfl

theorem pointwiseOperator_norm_le :
    ‖pointwiseOperator (K := K) (E := E) (F := F)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  simpa only [one_mul, pointwiseOperator_apply] using pointwiseLinear_norm_le A

theorem hasFDerivAt_postcomp [FiniteDimensional ℝ E]
    (f : C(E, F)) (Df : C(E, E →L[ℝ] F))
    (hDf : ∀ x, HasFDerivAt f (Df x) x) (φ : C(K, E)) :
    HasFDerivAt (fun ψ : C(K, E) ↦ f.comp ψ)
      (pointwiseLinear (Df.comp φ)) φ := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  let S := Metric.closedBall (0 : E) (‖φ‖ + 1)
  have hcompact : IsCompact S := isCompact_closedBall _ _
  obtain ⟨δ, hδ, hcontrol⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous Df.continuous.continuousOn) ε hε
  have hnear : ∀ᶠ ψ : C(K, E) in 𝓝 φ, ‖ψ - φ‖ < min 1 δ := by
    filter_upwards [Metric.ball_mem_nhds φ (lt_min zero_lt_one hδ)] with ψ hψ
    simpa only [Metric.mem_ball, dist_eq_norm] using hψ
  filter_upwards [hnear] with ψ hψ
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).2
  intro k
  have hφ : φ k ∈ S := by
    change dist (φ k) 0 ≤ ‖φ‖ + 1
    rw [dist_zero_right]
    exact (φ.norm_coe_le_norm k).trans (le_add_of_nonneg_right zero_le_one)
  have hψk : ‖ψ k - φ k‖ ≤ ‖ψ - φ‖ := (ψ - φ).norm_coe_le_norm k
  have hψS : ψ k ∈ S := by
    change dist (ψ k) 0 ≤ ‖φ‖ + 1
    rw [dist_zero_right]
    calc
      ‖ψ k‖ = ‖(ψ k - φ k) + φ k‖ := by rw [sub_add_cancel]
      _ ≤ ‖ψ k - φ k‖ + ‖φ k‖ := norm_add_le _ _
      _ ≤ 1 + ‖φ‖ := add_le_add (hψk.trans (lt_of_lt_of_le hψ (min_le_left _ _)).le)
        (φ.norm_coe_le_norm k)
      _ = ‖φ‖ + 1 := add_comm _ _
  have hsegment : segment ℝ (φ k) (ψ k) ⊆ S :=
    (convex_closedBall (0 : E) (‖φ‖ + 1)).segment_subset hφ hψS
  have hbound : ∀ x ∈ segment ℝ (φ k) (ψ k), ‖Df x - Df (φ k)‖ ≤ ε := by
    intro x hx
    apply le_of_lt
    have hdist : dist x (φ k) < δ := by
      rw [dist_eq_norm]
      exact (norm_sub_le_of_mem_segment hx).trans_lt
        (hψk.trans_lt (lt_of_lt_of_le hψ (min_le_right _ _)))
    simpa only [dist_eq_norm] using hcontrol x (hsegment hx) (φ k) hφ hdist
  have hrem := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun x (_ : x ∈ segment ℝ (φ k) (ψ k)) ↦ (hDf x).hasFDerivWithinAt)
    hbound (convex_segment (φ k) (ψ k))
    (left_mem_segment ℝ (φ k) (ψ k)) (right_mem_segment ℝ (φ k) (ψ k))
  exact hrem.trans (mul_le_mul_of_nonneg_left hψk hε.le)

theorem contDiff_postcomp_nat [FiniteDimensional ℝ E]
    (n : ℕ) (f : C(E, F)) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun φ : C(K, E) ↦ f.comp φ) := by
  induction n generalizing F with
  | zero => exact contDiff_zero.mpr f.continuous_postcomp
  | succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one] at hf ⊢
    obtain ⟨df, hdf, hderiv⟩ := contDiff_succ_iff_hasFDerivAt.mp hf
    let Df : C(E, E →L[ℝ] F) := ⟨df, hdf.continuous⟩
    refine contDiff_succ_iff_hasFDerivAt.mpr
      ⟨fun φ ↦ pointwiseLinear (Df.comp φ), ?_, fun φ ↦ hasFDerivAt_postcomp f Df hderiv φ⟩
    exact (pointwiseOperator (K := K) (E := E) (F := F)).contDiff.comp (ih Df hdf)

theorem contDiff_postcomp_smooth [FiniteDimensional ℝ E]
    (f : C(E, F)) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun φ : C(K, E) ↦ f.comp φ) :=
  contDiff_infty.mpr fun n ↦ contDiff_postcomp_nat n f (contDiff_infty.mp hf n)

end PoincareConjecture.Proofs.M09
