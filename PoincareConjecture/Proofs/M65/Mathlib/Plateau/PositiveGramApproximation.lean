import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Matrix
open scoped Topology ContDiff Convolution BigOperators Matrix.Norms.Elementwise

namespace Matrix

local instance : ContinuousENorm (Matrix (Fin 2) (Fin 2) ℝ) :=
  inferInstanceAs (ContinuousENorm (Fin 2 → Fin 2 → ℝ))

private theorem positive_integral {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {F : α → Matrix (Fin 2) (Fin 2) ℝ} (hF : Integrable F ν)
    (hpos : ∀ᵐ z ∂ν, (F z).PosSemidef) : (∫ z, F z ∂ν).PosSemidef := by
  let ev (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))
  have he (i j : Fin 2) : (∫ z, F z ∂ν) i j = ∫ z, F z i j ∂ν :=
    ((ev i j).integral_comp_comm hF).symm
  apply posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · apply IsHermitian.ext
    intro i j
    simp only [star_trivial, he]
    apply integral_congr_ae
    filter_upwards [hpos] with z hz
    exact hz.isHermitian.apply i j
  · intro v
    let L : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℝ :=
      ((dotProductBilin ℝ ℝ (star v)).comp ((mulVecBilin ℝ ℝ).flip v)).toContinuousLinearMap
    change 0 ≤ L (∫ z, F z ∂ν)
    erw [← L.integral_comp_comm hF]
    apply integral_nonneg_of_ae
    filter_upwards [hpos] with z hz
    exact hz.dotProduct_mulVec_nonneg v

private theorem positive_convolution (φ : ContDiffBump (0 : ℂ))
    {H : ℂ → Matrix (Fin 2) (Fin 2) ℝ} (hH : LocallyIntegrable H volume)
    {C : ℝ} (hbound : ∀ᵐ z ∂volume, (H z).PosSemidef ∧ ‖H z‖ ≤ C) (z : ℂ) :
    ((φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] H) z).PosSemidef ∧
      ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] H) z‖ ≤ C := by
  have hi := (φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (φ.continuous_normed (μ := volume)) hH z
  have hb := (quasiMeasurePreserving_sub_left_of_right_invariant volume z).ae hbound
  constructor
  · apply positive_integral hi
    filter_upwards [hb] with t ht
    exact ht.1.smul (φ.nonneg_normed t)
  · calc
      _ ≤ ∫ t, ‖φ.normed volume t • H (z - t)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t, φ.normed volume t * C := by
        apply integral_mono_ae hi.norm (φ.integrable_normed.mul_const C)
        filter_upwards [hb] with t ht
        change ‖φ.normed volume t • H (z - t)‖ ≤ φ.normed volume t * C
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t)]
        exact mul_le_mul_of_nonneg_left ht.2 (φ.nonneg_normed t)
      _ = C := by rw [integral_mul_const, φ.integral_normed, one_mul]






theorem exists_positive_annular_approximation
    (H : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (hH : LocallyIntegrable H volume)
    {C : ℝ} (hbound : ∀ᵐ z ∂volume, (H z).PosSemidef ∧ ‖H z‖ ≤ C) :
    ∃ G : ℕ → ℂ → Matrix (Fin 2) (Fin 2) ℝ,
      (∀ n, ContDiff ℝ ∞ (G n) ∧ HasCompactSupport (G n) ∧
        (∀ z, (G n z).PosSemidef ∧ ‖G n z‖ ≤ C) ∧
        ∃ a b : ℝ, 0 < a ∧ b < 1 ∧
          ∀ z, ‖z‖ ≤ a ∨ b ≤ ‖z‖ → G n z = 0) ∧
      ∀ᵐ z ∂volume, z ≠ 0 → ‖z‖ < 1 →
        Tendsto (fun n => G n z) atTop (𝓝 (H z)) := by
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
  have hε (n : ℕ) : 0 < ε n ∧ ε n < 1 := by
    dsimp only [ε]
    constructor
    · positivity
    · exact (div_lt_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_add_atTop_iff_nat 2).2 (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  let small (n : ℕ) : ContDiffBump (0 : ℂ) :=
    { rIn := ε n / 2
      rOut := ε n
      rIn_pos := half_pos (hε n).1
      rIn_lt_rOut := half_lt_self (hε n).1 }
  let large (n : ℕ) : ContDiffBump (0 : ℂ) :=
    { rIn := 1 - ε n
      rOut := 1 - ε n / 2
      rIn_pos := sub_pos.mpr (hε n).2
      rIn_lt_rOut := by linarith [(hε n).1] }
  let χ (n : ℕ) (z : ℂ) : ℝ := (1 - small n z) * large n z
  have hχ (n : ℕ) (z : ℂ) : 0 ≤ χ n z ∧ χ n z ≤ 1 := by
    have hs0 := (small n).nonneg (x := z)
    have hs1 := (small n).le_one (x := z)
    have hl0 := (large n).nonneg (x := z)
    have hl1 := (large n).le_one (x := z)
    dsimp only [χ]
    constructor
    · exact mul_nonneg (sub_nonneg.mpr hs1) hl0
    · nlinarith
  let Q (n : ℕ) := (small n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] H
  have hQ (n : ℕ) : ContDiff ℝ ∞ (Q n) :=
    (small n).hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (small n).contDiff_normed hH
  have hQbound (n : ℕ) (z : ℂ) : (Q n z).PosSemidef ∧ ‖Q n z‖ ≤ C :=
    positive_convolution (small n) hH hbound z
  let G (n : ℕ) (z : ℂ) := χ n z • Q n z
  refine ⟨G, ?_, ?_⟩
  · intro n
    refine ⟨?_, ?_, ?_, ε n / 2, 1 - ε n / 2, half_pos (hε n).1,
      by linarith [(hε n).1], ?_⟩
    · exact ((contDiff_const.sub (small n).contDiff).mul (large n).contDiff).smul (hQ n)
    · apply (large n).hasCompactSupport.mono
      intro z hz
      contrapose! hz
      simp only [Function.mem_support, ne_eq, not_not] at hz ⊢
      simp only [G, χ, hz, mul_zero, zero_smul]
    · intro z
      refine ⟨(hQbound n z).1.smul (hχ n z).1, ?_⟩
      change ‖χ n z • Q n z‖ ≤ C
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ n z).1]
      calc
        _ ≤ 1 * ‖Q n z‖ := mul_le_mul_of_nonneg_right (hχ n z).2 (norm_nonneg _)
        _ ≤ C := by simpa only [one_mul] using (hQbound n z).2
    · intro z hz
      rcases hz with hz | hz
      · have hs : small n z = 1 := (small n).one_of_mem_closedBall
          (mem_closedBall_zero_iff.mpr hz)
        simp only [G, χ, hs, sub_self, zero_mul, zero_smul]
      · have hl : large n z = 0 := (large n).zero_of_le_dist
          (by simpa only [dist_zero_right] using hz)
        simp only [G, χ, hl, mul_zero, zero_smul]
  · have hconv : ∀ᵐ z ∂volume, Tendsto (fun n => Q n z) atTop (𝓝 (H z)) :=
      ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hεlim
        (Eventually.of_forall fun n => (show (small n).rOut ≤ 2 * (small n).rIn by
          dsimp only [small]; linarith)) hH
    filter_upwards [hconv] with z hz hne hin
    have hsmall : ∀ᶠ n in atTop, ε n < ‖z‖ :=
      hεlim.eventually (gt_mem_nhds (norm_pos_iff.mpr hne))
    have hlarge : ∀ᶠ n in atTop, ε n < 1 - ‖z‖ :=
      hεlim.eventually (gt_mem_nhds (sub_pos.mpr hin))
    apply hz.congr'
    filter_upwards [hsmall, hlarge] with n hsn hln
    have hs : small n z = 0 := (small n).zero_of_le_dist
      (by simpa only [dist_zero_right] using hsn.le)
    have hl : large n z = 1 := (large n).one_of_mem_closedBall
      (mem_closedBall_zero_iff.mpr (by dsimp only [large]; linarith))
    simp only [G, χ, hs, hl, sub_zero, mul_one, one_smul]

end Matrix
