import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Normalize

set_option autoImplicit false

open Set Function NormedSpace
open scoped ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def radialFiberMap (f : (ℝ × E) × ℝ → ℝ) (p : ℝ × E) : ℝ × E :=
  (p.1, (1 + f ((p.1, normalize p.2), ‖p.2‖ - 1)) • normalize p.2)

@[simp] theorem radialFiberMap_apply_zero (f : (ℝ × E) × ℝ → ℝ) (z : ℝ) :
    radialFiberMap f (z, 0) = (z, 0) := by
  simp [radialFiberMap]

theorem radialFiberMap_eq_self (f : (ℝ × E) × ℝ → ℝ) (p : ℝ × E)
    (hf : f ((p.1, normalize p.2), ‖p.2‖ - 1) = ‖p.2‖ - 1) :
    radialFiberMap f p = p := by
  simp only [radialFiberMap, hf, show 1 + (‖p.2‖ - 1) = ‖p.2‖ by ring,
    norm_smul_normalize, Prod.mk.eta]

theorem radialFiberMap_apply_radial (f : (ℝ × E) × ℝ → ℝ) (z : ℝ)
    (q : E) (hq : ‖q‖ = 1) {r : ℝ} (hr : -1 < r) :
    radialFiberMap f (z, (1 + r) • q) = (z, (1 + f ((z, q), r)) • q) := by
  have hpos : 0 < 1 + r := by linarith
  simp [radialFiberMap, normalize_smul_of_pos hpos, normalize_eq_self_of_norm_eq_one hq,
    norm_smul, Real.norm_eq_abs, abs_of_pos hpos, hq]

theorem radialFiberMap_leftInverse (f g : (ℝ × E) × ℝ → ℝ)
    (hleft : ∀ z : ℝ, ∀ q : E, ‖q‖ = 1 → ∀ r : ℝ, -1 < r →
      g ((z, q), f ((z, q), r)) = r)
    (hpos : ∀ z : ℝ, ∀ q : E, ‖q‖ = 1 → ∀ r : ℝ, -1 < r →
      -1 < f ((z, q), r)) :
    LeftInverse (radialFiberMap g) (radialFiberMap f) := by
  rintro ⟨z, x⟩
  by_cases hx : x = 0
  · subst x
    simp only [radialFiberMap_apply_zero]
  · let q := normalize x
    let r := ‖x‖ - 1
    have hq : ‖q‖ = 1 := norm_normalize hx
    have hr : -1 < r := by dsimp only [r]; linarith [norm_pos_iff.mpr hx]
    have hrep : (1 + r) • q = x := by
      dsimp only [r, q]
      rw [show 1 + (‖x‖ - 1) = ‖x‖ by ring, norm_smul_normalize]
    rw [← hrep, radialFiberMap_apply_radial f z q hq hr,
      radialFiberMap_apply_radial g z q hq (hpos z q hq r hr), hleft z q hq r hr]

end Normed

theorem contDiff_radialFiberMap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : (ℝ × E) × ℝ → ℝ) (hf : ContDiff ℝ ∞ f) {w : ℝ} (hw : w < 1)
    (hfix : ∀ p : (ℝ × E) × ℝ, w ≤ |p.2| → f p = p.2) :
    ContDiff ℝ ∞ (radialFiberMap f) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.2 = 0
  · apply contDiffAt_id.congr_of_eventuallyEq
    have hnear : ∀ᶠ y : ℝ × E in nhds p, ‖y.2‖ < 1 - w :=
      continuous_snd.norm.continuousAt.eventually_lt continuousAt_const
        (by simpa only [hp, norm_zero] using sub_pos.mpr hw)
    filter_upwards [hnear] with y hy
    apply radialFiberMap_eq_self f y
    apply hfix
    change w ≤ |‖y.2‖ - 1|
    linarith [neg_le_abs (‖y.2‖ - 1)]
  · have hn : ContDiffAt ℝ ∞ (fun y : ℝ × E => ‖y.2‖) p :=
      (contDiffAt_norm ℝ hp).comp p contDiffAt_snd
    have hq : ContDiffAt ℝ ∞ (fun y : ℝ × E => normalize y.2) p :=
      (hn.inv (norm_ne_zero_iff.mpr hp)).smul contDiffAt_snd
    exact contDiffAt_fst.prodMk
      ((contDiffAt_const.add (hf.contDiffAt.comp p
        ((contDiffAt_fst.prodMk hq).prodMk (hn.sub contDiffAt_const)))).smul hq)

end Poincare.Manifold.Schoenflies.Plane
