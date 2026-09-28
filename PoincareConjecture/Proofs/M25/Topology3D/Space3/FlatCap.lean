import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false

open Set Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_smooth_positive_profile [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b U) (hpos : ∀ x ∈ U, 0 < b x) :
    ∃ a : E → ℝ, ContDiff ℝ ∞ a ∧ (∀ x, 0 < a x) ∧
      (∀ᶠ x in 𝓝ˢ K, a x = b x) ∧ ∀ x ∉ U, a x = 1 := by
  obtain ⟨ρ, hρ, _, hs, hnear, hrange⟩ := exists_compact_smooth_cutoff hK hU hKU
  let a : E → ℝ := fun x => ρ x * (b x - 1) + 1
  have ha : ContDiff ℝ ∞ a :=
    (contDiff_cutoff_smul hU ρ hρ hs (fun x => b x - 1)
      (hb.sub contDiffOn_const)).add contDiff_const
  refine ⟨a, ha, ?_, ?_, ?_⟩
  · intro x
    by_cases hzero : ρ x = 0
    · simp only [a, hzero, zero_mul, zero_add, zero_lt_one]
    · have hρpos : 0 < ρ x := lt_of_le_of_ne (hrange x).1 (Ne.symm hzero)
      have hprod : 0 < ρ x * b x := mul_pos hρpos (hpos x (hs (subset_tsupport ρ hzero)))
      dsimp [a]
      nlinarith [(hrange x).2]
  · filter_upwards [hnear] with x hx
    dsimp [a]
    rw [hx, one_mul, sub_add_cancel]
  · intro x hx
    have hzero : ρ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
    simp only [a, hzero, zero_mul, zero_add]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smooth_profile_between [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b U) (hb1 : ∀ x ∈ U, 1 ≤ b x) :
    ∃ a : E → ℝ, ContDiff ℝ ∞ a ∧ (∀ x, 1 ≤ a x) ∧
      (∀ᶠ x in 𝓝ˢ K, a x = b x) ∧ (∀ x ∉ U, a x = 1) ∧
      ∀ x ∈ U, a x ≤ b x := by
  obtain ⟨ρ, hρ, _, hs, hnear, hrange⟩ := exists_compact_smooth_cutoff hK hU hKU
  let a : E → ℝ := fun x => ρ x * (b x - 1) + 1
  have ha : ContDiff ℝ ∞ a :=
    (contDiff_cutoff_smul hU ρ hρ hs (fun x => b x - 1)
      (hb.sub contDiffOn_const)).add contDiff_const
  have hfar (x : E) (hx : x ∉ U) : a x = 1 := by
    have hzero : ρ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
    simp only [a, hzero, zero_mul, zero_add]
  refine ⟨a, ha, ?_, ?_, hfar, ?_⟩
  · intro x
    by_cases hx : x ∈ U
    · exact le_add_of_nonneg_left (mul_nonneg (hrange x).1 (sub_nonneg.mpr (hb1 x hx)))
    · exact (hfar x hx).ge
  · filter_upwards [hnear] with x hx
    dsimp [a]
    rw [hx, one_mul, sub_add_cancel]
  · intro x hx
    have h := mul_le_mul_of_nonneg_right (hrange x).2 (sub_nonneg.mpr (hb1 x hx))
    dsimp [a]
    linarith

variable (a : E → ℝ) (ha : ContDiff ℝ ∞ a) (ha0 : ∀ x, a x ≠ 0)

noncomputable def fiberScalingDiffeomorph :
    Diffeomorph 𝓘(ℝ, E × F) 𝓘(ℝ, E × F) (E × F) (E × F) ∞ where
  toEquiv := {
    toFun := fun p => (p.1, a p.1 • p.2)
    invFun := fun p => (p.1, (a p.1)⁻¹ • p.2)
    left_inv := fun p => by
      dsimp
      rw [smul_smul, inv_mul_cancel₀ (ha0 p.1), one_smul]
    right_inv := fun p => by
      dsimp
      rw [smul_smul, mul_inv_cancel₀ (ha0 p.1), one_smul] }
  contMDiff_toFun :=
    (contDiff_fst.prodMk ((ha.comp contDiff_fst).smul contDiff_snd)).contMDiff
  contMDiff_invFun :=
    (contDiff_fst.prodMk (((ha.comp contDiff_fst).inv
      (fun p => ha0 p.1)).smul contDiff_snd)).contMDiff

@[simp] theorem fiberScalingDiffeomorph_apply (p : E × F) :
    fiberScalingDiffeomorph a ha ha0 p = (p.1, a p.1 • p.2) := rfl

@[simp] theorem fiberScalingDiffeomorph_symm_apply (p : E × F) :
    (fiberScalingDiffeomorph a ha ha0).symm p = (p.1, (a p.1)⁻¹ • p.2) := rfl

end PoincareConjecture.M25.Topology3D
