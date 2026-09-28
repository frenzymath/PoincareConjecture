import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.NonlinearJets
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped ContDiff NNReal

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

private theorem linear_tail_fderiv {S : E × Z → ℝ} {a : E → Z →L[ℝ] ℝ}
    (hS : ContDiff ℝ ∞ S) (ha : ContDiff ℝ ∞ a) (x v : E) (z w : Z) :
    fderiv ℝ (fun p : E × Z => S p + a p.1 p.2) (x, z) (v, w) =
      fderiv ℝ S (x, z) (v, w) + fderiv ℝ a x v z + a x w := by
  have haf : HasFDerivAt (fun p : E × Z => a p.1)
      ((fderiv ℝ a x).comp (ContinuousLinearMap.fst ℝ E Z)) (x, z) :=
    (ha.differentiable (by simp) x).hasFDerivAt.comp (x, z) hasFDerivAt_fst
  have hzs : HasFDerivAt (fun p : E × Z => p.2)
      (ContinuousLinearMap.snd ℝ E Z) (x, z) := hasFDerivAt_snd
  have hl := haf.clm_apply hzs
  have ht := (hS.differentiable (by simp) (x, z)).hasFDerivAt.add hl
  simp only [Pi.add_def] at ht
  rw [ht.fderiv]
  change fderiv ℝ S (x, z) (v, w) + (a x w + fderiv ℝ a x v z) = _
  ring

private theorem linear_tail_valueJet {S : E × Z → ℝ} {a : E → Z →L[ℝ] ℝ}
    (hS : ContDiff ℝ ∞ S) (ha : ContDiff ℝ ∞ a) (x : E) (z : Z) :
    nonlinearValueJet (fun p : E × Z => S p + a p.1 p.2) x z =
      (fderiv ℝ S (x, z)).comp (ContinuousLinearMap.inr ℝ E Z) + a x := by
  ext w
  change fderiv ℝ (fun p : E × Z => S p + a p.1 p.2) (x, z) (0, w) = _
  rw [linear_tail_fderiv hS ha]
  simp only [map_zero, zero_apply, add_zero, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]

private theorem norm_restrict_value_le (L : E × Z →L[ℝ] ℝ) :
    ‖L.comp (ContinuousLinearMap.inr ℝ E Z)‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro w
  simpa using L.le_opNorm (0, w)

omit [NormedSpace ℝ E] in
private theorem linear_tail_value_bound {S : E × Z → ℝ} {a : E → Z →L[ℝ] ℝ}
    {K : ℝ≥0} {A : ℝ} (hK : LipschitzWith K S) (hA : ∀ x, ‖a x‖ ≤ A)
    (x : E) (z w : Z) :
    ‖(S (x, z) + a x z) - (S (x, w) + a x w)‖ ≤ ((K : ℝ) + A) * ‖z - w‖ := by
  have hs : ‖S (x, z) - S (x, w)‖ ≤ (K : ℝ) * ‖z - w‖ := by
    simpa [dist_eq_norm, Prod.norm_def] using hK.dist_le_mul (x, z) (x, w)
  have he : (S (x, z) + a x z) - (S (x, w) + a x w) =
      (S (x, z) - S (x, w)) + a x (z - w) := by rw [map_sub]; ring
  rw [he]
  calc
    _ ≤ ‖S (x, z) - S (x, w)‖ + ‖a x (z - w)‖ := norm_add_le _ _
    _ ≤ (K : ℝ) * ‖z - w‖ + A * ‖z - w‖ := add_le_add hs
      (((a x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _)))
    _ = ((K : ℝ) + A) * ‖z - w‖ := by ring

private theorem linear_tail_space_bound {S : E × Z → ℝ} {a : E → Z →L[ℝ] ℝ}
    (hS : ContDiff ℝ ∞ S) (ha : ContDiff ℝ ∞ a) {L : ℝ≥0} {B : ℝ}
    (hL : LipschitzWith L (fderiv ℝ S)) (hB0 : 0 ≤ B) (hB : ∀ x, ‖fderiv ℝ a x‖ ≤ B)
    (x : E) (z w : Z) (v : E) (hv : ‖v‖ ≤ 1) :
    ‖nonlinearSpaceJet (fun p : E × Z => S p + a p.1 p.2) x z v -
      nonlinearSpaceJet (fun p : E × Z => S p + a p.1 p.2) x w v‖ ≤
        ((L : ℝ) + B) * ‖z - w‖ := by
    have he : nonlinearSpaceJet (fun p : E × Z => S p + a p.1 p.2) x z v -
        nonlinearSpaceJet (fun p : E × Z => S p + a p.1 p.2) x w v =
        (fderiv ℝ S (x, z) - fderiv ℝ S (x, w)) (v, 0) +
          fderiv ℝ a x v (z - w) := by
      change fderiv ℝ (fun p : E × Z => S p + a p.1 p.2) (x, z) (v, 0) -
        fderiv ℝ (fun p : E × Z => S p + a p.1 p.2) (x, w) (v, 0) = _
      rw [linear_tail_fderiv hS ha, linear_tail_fderiv hS ha]
      simp only [map_zero, add_zero, sub_apply, map_sub]
      ring
    have hs : ‖(fderiv ℝ S (x, z) - fderiv ℝ S (x, w)) (v, 0)‖ ≤
        (L : ℝ) * ‖z - w‖ := by
      have h := (fderiv ℝ S (x, z) - fderiv ℝ S (x, w)).le_opNorm (v, 0)
      simp only [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg v)] at h
      have hd : ‖fderiv ℝ S (x, z) - fderiv ℝ S (x, w)‖ ≤ (L : ℝ) * ‖z - w‖ := by
        simpa [dist_eq_norm, Prod.norm_def] using hL.dist_le_mul (x, z) (x, w)
      exact h.trans ((mul_le_mul hd hv (norm_nonneg v)
        (mul_nonneg L.coe_nonneg (norm_nonneg _))).trans_eq (mul_one _))
    have had : ‖fderiv ℝ a x v‖ ≤ B :=
      ((fderiv ℝ a x).le_opNorm v).trans
        ((mul_le_mul (hB x) hv (norm_nonneg v) hB0).trans_eq (mul_one _))
    rw [he]
    calc
      _ ≤ ‖(fderiv ℝ S (x, z) - fderiv ℝ S (x, w)) (v, 0)‖ +
          ‖fderiv ℝ a x v (z - w)‖ := norm_add_le _ _
      _ ≤ (L : ℝ) * ‖z - w‖ + B * ‖z - w‖ := add_le_add hs
        (((fderiv ℝ a x v).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right had (norm_nonneg _)))
      _ = ((L : ℝ) + B) * ‖z - w‖ := by ring

private theorem linear_tail_valueJet_bound {S : E × Z → ℝ} {a : E → Z →L[ℝ] ℝ}
    (hS : ContDiff ℝ ∞ S) (ha : ContDiff ℝ ∞ a) {M A : ℝ}
    (hM : ∀ p, ‖fderiv ℝ S p‖ ≤ M) (hA : ∀ x, ‖a x‖ ≤ A) (x : E) (z : Z) :
    ‖nonlinearValueJet (fun p : E × Z => S p + a p.1 p.2) x z‖ ≤ M + A := by
    rw [linear_tail_valueJet hS ha]
    exact (norm_add_le _ _).trans
      (add_le_add ((norm_restrict_value_le _).trans (hM (x, z))) (hA x))

private theorem linear_tail_valueJet_difference {S : E × Z → ℝ} {a : E → Z →L[ℝ] ℝ}
    (hS : ContDiff ℝ ∞ S) (ha : ContDiff ℝ ∞ a) {L : ℝ≥0}
    (hL : LipschitzWith L (fderiv ℝ S)) (x : E) (z w : Z) :
    ‖nonlinearValueJet (fun p : E × Z => S p + a p.1 p.2) x z -
      nonlinearValueJet (fun p : E × Z => S p + a p.1 p.2) x w‖ ≤ (L : ℝ) * ‖z - w‖ := by
    rw [linear_tail_valueJet hS ha, linear_tail_valueJet hS ha]
    have he : (fderiv ℝ S (x, z)).comp (ContinuousLinearMap.inr ℝ E Z) + a x -
        ((fderiv ℝ S (x, w)).comp (ContinuousLinearMap.inr ℝ E Z) + a x) =
        (fderiv ℝ S (x, z) - fderiv ℝ S (x, w)).comp (ContinuousLinearMap.inr ℝ E Z) := by
      ext y
      simp only [add_apply, sub_apply, ContinuousLinearMap.comp_apply]
      ring
    rw [he]
    apply (norm_restrict_value_le _).trans
    simpa [dist_eq_norm, Prod.norm_def] using hL.dist_le_mul (x, z) (x, w)

theorem compact_linear_tail_jet_bounds {S : E × Z → ℝ} {a : E → Z →L[ℝ] ℝ}
    (hS : ContDiff ℝ ∞ S) (hcS : HasCompactSupport S)
    (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ x z w, ‖(S (x, z) + a x z) - (S (x, w) + a x w)‖ ≤ C * ‖z - w‖) ∧
      (∀ x z w v, ‖v‖ ≤ 1 →
        ‖nonlinearSpaceJet (fun p : E × Z => S p + a p.1 p.2) x z v -
          nonlinearSpaceJet (fun p : E × Z => S p + a p.1 p.2) x w v‖ ≤ C * ‖z - w‖) ∧
      (∀ x z, ‖nonlinearValueJet (fun p : E × Z => S p + a p.1 p.2) x z‖ ≤ C) ∧
      (∀ x z w,
        ‖nonlinearValueJet (fun p : E × Z => S p + a p.1 p.2) x z -
          nonlinearValueJet (fun p : E × Z => S p + a p.1 p.2) x w‖ ≤ C * ‖z - w‖) := by
  have hdS : ContDiff ℝ ∞ (fderiv ℝ S) := hS.fderiv_right (by simp)
  have hda : ContDiff ℝ ∞ (fderiv ℝ a) := ha.fderiv_right (by simp)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ p, ‖fderiv ℝ S p‖ ≤ M :=
    HasCompactSupport.exists_bound_of_continuous
      (f := fderiv ℝ S) (hcS.fderiv ℝ) hdS.continuous
  obtain ⟨A, hA⟩ : ∃ A : ℝ, ∀ x, ‖a x‖ ≤ A :=
    HasCompactSupport.exists_bound_of_continuous (f := a) hca ha.continuous
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x, ‖fderiv ℝ a x‖ ≤ B :=
    HasCompactSupport.exists_bound_of_continuous
      (f := fderiv ℝ a) (hca.fderiv ℝ) hda.continuous
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0, LipschitzWith K S :=
    ContDiff.lipschitzWith_of_hasCompactSupport hcS hS (by simp)
  obtain ⟨L, hL⟩ : ∃ L : ℝ≥0, LipschitzWith L (fderiv ℝ S) :=
    ContDiff.lipschitzWith_of_hasCompactSupport (hcS.fderiv ℝ) hdS (by simp)
  have hM0 : 0 ≤ M := (norm_nonneg (fderiv ℝ S (0, 0))).trans (hM (0, 0))
  have hA0 : 0 ≤ A := (norm_nonneg (a 0)).trans (hA 0)
  have hB0 : 0 ≤ B := (norm_nonneg (fderiv ℝ a 0)).trans (hB 0)
  let C : ℝ := M + A + B + K + L
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hKA : (K : ℝ) + A ≤ C := by dsimp [C]; linarith only [hM0, hB0, L.coe_nonneg]
  have hLB : (L : ℝ) + B ≤ C := by dsimp [C]; linarith only [hM0, hA0, K.coe_nonneg]
  have hMA : M + A ≤ C := by dsimp [C]; linarith only [hB0, K.coe_nonneg, L.coe_nonneg]
  have hLC : (L : ℝ) ≤ C := by dsimp [C]; linarith only [hM0, hA0, hB0, K.coe_nonneg]
  refine ⟨C, hC, ?_, ?_, ?_, ?_⟩
  · intro x z w
    exact (linear_tail_value_bound hK hA x z w).trans
      (mul_le_mul_of_nonneg_right hKA (norm_nonneg _))
  · intro x z w v hv
    exact (linear_tail_space_bound hS ha hL hB0 hB x z w v hv).trans
      (mul_le_mul_of_nonneg_right hLB (norm_nonneg _))
  · intro x z
    exact (linear_tail_valueJet_bound hS ha hM hA x z).trans hMA
  · intro x z w
    exact (linear_tail_valueJet_difference hS ha hL x z w).trans
      (mul_le_mul_of_nonneg_right hLC (norm_nonneg _))

end PoincareConjecture.M35.Uniqueness.Heat
