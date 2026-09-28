import PoincareConjecture.Proofs.M35.RadialGauge.RadialProfileCalculus
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

theorem radialTrace_iteratedDeriv_norm_le {u : V → ℝ} (hu : ContDiff ℝ ∞ u)
    {e : V} (he : ‖e‖ = 1) (j : ℕ) (r : ℝ) :
    |iteratedDeriv j (fun s : ℝ => u (s • e)) r| ≤
      ‖iteratedFDeriv ℝ j u (r • e)‖ := by
  let I : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight e
  have h := I.iteratedFDeriv_comp_right hu r
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
  change iteratedFDeriv ℝ j (fun s : ℝ => u (s • e)) r = _ at h
  rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv, h]
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro v
  change ‖iteratedFDeriv ℝ j u (r • e) (fun i => v i • e)‖ ≤ _
  simpa only [norm_smul, he, mul_one] using
    (iteratedFDeriv ℝ j u (r • e)).le_opNorm (fun i => v i • e)

theorem radialTrace_weighted_jet_le {u : V → ℝ} (hu : ContDiff ℝ ∞ u)
    {e : V} (he : ‖e‖ = 1) (j : ℕ) (r : ℝ) :
    (1 + |r|) * |iteratedDeriv j (fun s : ℝ => u (s • e)) r| ≤
      (1 + ‖r • e‖) * ‖iteratedFDeriv ℝ j u (r • e)‖ := by
  simpa only [norm_smul, Real.norm_eq_abs, he, mul_one] using
    mul_le_mul_of_nonneg_left (radialTrace_iteratedDeriv_norm_le hu he j r)
      (show 0 ≤ 1 + |r| by positivity)

theorem radialTrace_weighted_jet_vanishes_uniformly
    {A : Type*} {u : A → V → ℝ} (hu : ∀ a, ContDiff ℝ ∞ (u a))
    {e : V} (he : ‖e‖ = 1) (j : ℕ)
    (hend : ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℝ, 0 ≤ R ∧
      ∀ a x, R ≤ ‖x‖ → (1 + ‖x‖) * ‖iteratedFDeriv ℝ j (u a) x‖ ≤ epsilon) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℝ, 0 ≤ R ∧
      ∀ a r, R ≤ |r| →
        (1 + |r|) * |iteratedDeriv j (fun s : ℝ => u a (s • e)) r| ≤ epsilon := by
  intro epsilon hepsilon
  obtain ⟨R, hR, hb⟩ := hend epsilon hepsilon
  refine ⟨R, hR, fun a r hr => ?_⟩
  apply (radialTrace_weighted_jet_le (hu a) he j r).trans
  apply hb a (r • e)
  simpa only [norm_smul, Real.norm_eq_abs, he, mul_one] using hr

end PoincareConjecture.M35.RadialGauge
