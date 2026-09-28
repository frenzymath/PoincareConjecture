import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Module

set_option autoImplicit false

open Function
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def roundedCorner (ρ : ℝ → ℝ) (p u v : E) (t : ℝ) : E :=
  p + ((t - ρ t) / 2) • u + ((t + ρ t) / 2) • v

theorem contDiff_roundedCorner {ρ : ℝ → ℝ} {p u v : V → E}
    (hρ : ContDiff ℝ ∞ ρ) (hp : ContDiff ℝ ∞ p)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (fun x : V × ℝ => roundedCorner ρ (p x.1) (u x.1) (v x.1) x.2) :=
  ((hp.comp contDiff_fst).add
    (((contDiff_snd.sub (hρ.comp contDiff_snd)).div_const 2).smul
      (hu.comp contDiff_fst))).add
    (((contDiff_snd.add (hρ.comp contDiff_snd)).div_const 2).smul
      (hv.comp contDiff_fst))

theorem hasDerivAt_roundedCorner {ρ : ℝ → ℝ} (p u v : E) {t : ℝ}
    (hρ : DifferentiableAt ℝ ρ t) :
    HasDerivAt (roundedCorner ρ p u v)
      (((1 - deriv ρ t) / 2) • u + ((1 + deriv ρ t) / 2) • v) t :=
  ((((hasDerivAt_id t).sub hρ.hasDerivAt).div_const 2).smul_const u).const_add p |>.add
    ((((hasDerivAt_id t).add hρ.hasDerivAt).div_const 2).smul_const v)

theorem roundedCorner_tail_bounds {ρ : ℝ → ℝ} (p u v : E) {δ : ℝ}
    (hδ : 0 < δ) (htail : ∀ t, δ ≤ |t| → ρ t = |t|)
    (hbound : ∀ t, |t| ≤ ρ t ∧ ρ t ≤ |t| + δ) :
    (∀ t, t ≤ -δ → roundedCorner ρ p u v t = p + t • u) ∧
    (∀ t, δ ≤ t → roundedCorner ρ p u v t = p + t • v) ∧
    ∀ t, dist (roundedCorner ρ p u v t)
      (if t ≤ 0 then p + t • u else p + t • v) ≤ δ / 2 * ‖v - u‖ := by
  have hpiece (t : ℝ) : roundedCorner abs p u v t =
      (if t ≤ 0 then p + t • u else p + t • v) := by
    by_cases ht : t ≤ 0
    · rw [if_pos ht, roundedCorner, abs_of_nonpos ht]
      module
    · rw [if_neg ht, roundedCorner, abs_of_pos (lt_of_not_ge ht)]
      module
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have ht0 : t ≤ 0 := by linarith
    have htδ : δ ≤ |t| := by rw [abs_of_nonpos ht0]; linarith
    rw [roundedCorner, htail t htδ, abs_of_nonpos ht0]
    module
  · intro t ht
    have ht0 : 0 ≤ t := le_trans hδ.le ht
    have htδ : δ ≤ |t| := by rwa [abs_of_nonneg ht0]
    rw [roundedCorner, htail t htδ, abs_of_nonneg ht0]
    module
  · intro t
    have heq : roundedCorner ρ p u v t - roundedCorner abs p u v t =
        ((ρ t - |t|) / 2) • (v - u) := by
      dsimp [roundedCorner]
      module
    have hnonneg : 0 ≤ (ρ t - |t|) / 2 := by linarith [(hbound t).1]
    have hle : (ρ t - |t|) / 2 ≤ δ / 2 := by linarith [(hbound t).2]
    rw [← hpiece t, dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hnonneg]
    exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)

theorem strictMono_roundedCorner_projection {ρ : ℝ → ℝ} (p u v : E)
    (hρ : Differentiable ℝ ρ) (hbound : ∀ t, |deriv ρ t| ≤ 1)
    (ℓ : E →L[ℝ] ℝ) (hu : 0 < ℓ u) (hv : 0 < ℓ v) :
    (∀ t, 0 < ℓ (deriv (roundedCorner ρ p u v) t)) ∧
    StrictMono (ℓ ∘ roundedCorner ρ p u v) ∧ Injective (roundedCorner ρ p u v) := by
  have hpos (t : ℝ) :
      0 < ℓ (((1 - deriv ρ t) / 2) • u + ((1 + deriv ρ t) / 2) • v) := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rcases abs_le.mp (hbound t) with ⟨hl, hr⟩
    have ha : 0 ≤ (1 - deriv ρ t) / 2 := by linarith
    have hb : 0 ≤ (1 + deriv ρ t) / 2 := by linarith
    by_cases ha0 : 0 < (1 - deriv ρ t) / 2
    · exact add_pos_of_pos_of_nonneg (mul_pos ha0 hu) (mul_nonneg hb hv.le)
    · have heq : (1 - deriv ρ t) / 2 = 0 := le_antisymm (le_of_not_gt ha0) ha
      have heq' : (1 + deriv ρ t) / 2 = 1 := by linarith
      simpa only [heq, heq', zero_mul, one_mul, zero_add] using hv
  have hmono : StrictMono (ℓ ∘ roundedCorner ρ p u v) :=
    strictMono_of_hasDerivAt_pos
      (fun t => ℓ.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_roundedCorner p u v (hρ t))) hpos
  refine ⟨?_, hmono, ?_⟩
  · intro t
    rw [(hasDerivAt_roundedCorner p u v (hρ t)).deriv]
    exact hpos t
  · intro s t hst
    exact hmono.injective (congrArg ℓ hst)

end PoincareConjecture.M25.Topology3D
