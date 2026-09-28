import PoincareConjecture.Proofs.M40.Mathlib.LipschitzSmoothing
import Mathlib.Tactic.Module












set_option autoImplicit false

open Function Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace PoincareConjecture.M40

variable {E F : Type*} [PseudoMetricSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



def cutoffBlend (ρ : E → ℝ) (f g : E → F) : E → F :=
  fun x => ρ x • g x + (1 - ρ x) • f x



theorem cutoffBlend_eq_left {ρ : E → ℝ} {f g : E → F} {x : E}
    (hρ : ρ x = 0) : cutoffBlend ρ f g x = f x := by
  simp [cutoffBlend, hρ]



theorem cutoffBlend_eq_right {ρ : E → ℝ} {f g : E → F} {x : E}
    (hρ : ρ x = 1) : cutoffBlend ρ f g x = g x := by
  simp [cutoffBlend, hρ]






theorem cutoffBlend_lipschitzOn {ρ : E → ℝ} {f g : E → F}
    {U : Set E} {L A δ : ℝ≥0}
    (hρ : LipschitzOnWith A ρ U) (hρrange : ∀ x ∈ U, ρ x ∈ Icc 0 1)
    (hf : LipschitzOnWith L f U) (hg : LipschitzOnWith L g U)
    (hclose : ∀ x ∈ U, dist (g x) (f x) ≤ δ) :
    LipschitzOnWith (L + A * δ) (cutoffBlend ρ f g) U := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hρx0 := (hρrange x hx).1
  have hρx1 := (hρrange x hx).2
  have hρxcomp : 0 ≤ 1 - ρ x := sub_nonneg.mpr hρx1
  have hdecomp : cutoffBlend ρ f g x - cutoffBlend ρ f g y =
      ρ x • (g x - g y) + (1 - ρ x) • (f x - f y) +
        (ρ x - ρ y) • (g y - f y) := by
    dsimp [cutoffBlend]
    module
  rw [dist_eq_norm, hdecomp]
  calc
    ‖ρ x • (g x - g y) + (1 - ρ x) • (f x - f y) +
        (ρ x - ρ y) • (g y - f y)‖
        ≤ ‖ρ x • (g x - g y) + (1 - ρ x) • (f x - f y)‖ +
            ‖(ρ x - ρ y) • (g y - f y)‖ := norm_add_le _ _
    _ ≤ ‖ρ x • (g x - g y)‖ + ‖(1 - ρ x) • (f x - f y)‖ +
          ‖(ρ x - ρ y) • (g y - f y)‖ := by gcongr; exact norm_add_le _ _
    _ = ρ x * dist (g x) (g y) + (1 - ρ x) * dist (f x) (f y) +
          dist (ρ x) (ρ y) * dist (g y) (f y) := by
      rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hρx0,
        Real.norm_of_nonneg (sub_nonneg.mpr hρx1)]
      simp only [dist_eq_norm]
    _ ≤ ρ x * ((L : ℝ) * dist x y) +
          (1 - ρ x) * ((L : ℝ) * dist x y) +
          ((A : ℝ) * dist x y) * δ := by
      gcongr
      · exact hg.dist_le_mul x hx y hy
      · exact hf.dist_le_mul x hx y hy
      · exact hρ.dist_le_mul x hx y hy
      · exact hclose y hy
    _ = (L + A * δ : ℝ≥0) * dist x y := by
      push_cast
      ring





theorem cutoffBlend_dist_le {ρ : E → ℝ} {f g : E → F} {x : E} {ε : ℝ}
    (hρ : ρ x ∈ Icc 0 1) (hclose : dist (g x) (f x) ≤ ε) :
    dist (cutoffBlend ρ f g x) (f x) ≤ ε := by
  have heq : cutoffBlend ρ f g x - f x = ρ x • (g x - f x) := by
    dsimp [cutoffBlend]
    module
  rw [dist_eq_norm, heq, norm_smul, Real.norm_of_nonneg hρ.1]
  calc
    ρ x * ‖g x - f x‖ ≤ 1 * ‖g x - f x‖ :=
      mul_le_mul_of_nonneg_right hρ.2 (norm_nonneg _)
    _ ≤ ε := by simpa only [one_mul, ← dist_eq_norm] using hclose




def cutoffCorrection (ρ : E → ℝ) (f : E → F) (v : F) : E → F :=
  fun x => f x + ρ x • v




theorem cutoffCorrection_apply_base {ρ : E → ℝ} {f : E → F}
    {b : E} (hρ : ρ b = 1) (y : F) :
    cutoffCorrection ρ f (y - f b) b = y := by
  simp [cutoffCorrection, hρ]






theorem cutoffCorrection_lipschitzOn {ρ : E → ℝ} {f : E → F}
    {U : Set E} {L A : ℝ≥0}
    (hρ : LipschitzOnWith A ρ U) (hf : LipschitzOnWith L f U) (v : F) :
    LipschitzOnWith (L + A * ‖v‖₊) (cutoffCorrection ρ f v) U := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hdecomp : cutoffCorrection ρ f v x - cutoffCorrection ρ f v y =
      (f x - f y) + (ρ x - ρ y) • v := by
    dsimp [cutoffCorrection]
    module
  rw [dist_eq_norm, hdecomp]
  calc
    ‖(f x - f y) + (ρ x - ρ y) • v‖
        ≤ ‖f x - f y‖ + ‖(ρ x - ρ y) • v‖ := norm_add_le _ _
    _ = dist (f x) (f y) + dist (ρ x) (ρ y) * ‖v‖ := by
      rw [norm_smul]
      simp only [dist_eq_norm]
    _ ≤ (L : ℝ) * dist x y + ((A : ℝ) * dist x y) * ‖v‖ := by
      gcongr
      · exact hf.dist_le_mul x hx y hy
      · exact hρ.dist_le_mul x hx y hy
    _ = (L + A * ‖v‖₊ : ℝ≥0) * dist x y := by
      push_cast
      ring





theorem cutoffCorrection_dist_le {ρ : E → ℝ} {f : E → F} {x : E}
    (hρ : ρ x ∈ Icc 0 1) (v : F) :
    dist (cutoffCorrection ρ f v x) (f x) ≤ ‖v‖ := by
  simp only [cutoffCorrection, dist_eq_norm, add_sub_cancel_left, norm_smul]
  rw [Real.norm_of_nonneg hρ.1]
  exact (mul_le_mul_of_nonneg_right hρ.2 (norm_nonneg v)).trans_eq (one_mul _)

section Smooth

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]



theorem cutoffBlend_contDiffOn {ρ : V → ℝ} {f g : V → F} {U : Set V}
    (hρ : ContDiffOn ℝ ∞ ρ U) (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (cutoffBlend ρ f g) U := by
  exact (hρ.smul hg).add ((contDiffOn_const.sub hρ).smul hf)



theorem cutoffCorrection_contDiffOn {ρ : V → ℝ} {f : V → F} {U : Set V}
    (hρ : ContDiffOn ℝ ∞ ρ U) (hf : ContDiffOn ℝ ∞ f U) (v : F) :
    ContDiffOn ℝ ∞ (cutoffCorrection ρ f v) U := by
  exact hf.add (hρ.smul contDiffOn_const)

end Smooth

end PoincareConjecture.M40
