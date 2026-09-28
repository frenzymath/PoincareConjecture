import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.ComparisonTest
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

open Set Filter
open scoped Topology NNReal

namespace Poincare.Analysis.Elliptic

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem compact_lipschitz_product
    {O : Set E} {u φ : E → ℝ} {A B : ℝ≥0}
    (hu : LipschitzOnWith A u O) (huB : ∀ x ∈ O, |u x| ≤ B)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) :
    ∃ C : ℝ≥0, LipschitzWith C (fun x => φ x * u x) := by
  obtain ⟨w, hw, heq⟩ := hu.extend_real
  let z : E → ℝ := fun x => max (-(B : ℝ)) (min (B : ℝ) (w x))
  have hz : LipschitzWith A z := (hw.const_min _).const_max _
  have hzB (x) : |z x| ≤ B := abs_le.mpr
    ⟨le_max_left _ _, max_le (neg_le_self B.coe_nonneg) (min_le_left _ _)⟩
  have hprod : (fun x => φ x * z x) = (fun x => φ x * u x) := by
    funext x
    by_cases hx : φ x = 0
    · simp only [hx, zero_mul]
    · have hxO := hφO (subset_tsupport _ hx)
      have hb := abs_le.mp (huB x hxO)
      simp only [z, ← heq hxO, min_eq_right hb.2, max_eq_right hb.1]
  rw [← hprod]
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ (by simp)
  obtain ⟨D, hD⟩ := hφc.exists_bound_of_continuous hφ.continuous
  let D' : ℝ≥0 := ⟨max D 0, le_max_right _ _⟩
  have hD' (x) : |φ x| ≤ D' := (hD x).trans (le_max_left _ _)
  refine ⟨D' * A + B * C, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hp := hC.dist_le_mul x y
  have hq := hz.dist_le_mul x y
  simp only [Real.dist_eq] at hp hq ⊢
  calc
    |φ x * z x - φ y * z y| = |φ x * (z x - z y) + z y * (φ x - φ y)| := by ring_nf
    _ ≤ |φ x * (z x - z y)| + |z y * (φ x - φ y)| := abs_add_le _ _
    _ = |φ x| * |z x - z y| + |z y| * |φ x - φ y| := by rw [abs_mul, abs_mul]
    _ ≤ D' * (A * dist x y) + B * (C * dist x y) :=
      add_le_add (mul_le_mul (hD' x) hq (abs_nonneg _) D'.coe_nonneg)
        (mul_le_mul (hzB y) hp (abs_nonneg _) B.coe_nonneg)
    _ = ((D' * A + B * C : ℝ≥0) : ℝ) * dist x y := by push_cast; ring

theorem compact_lipschitz_exp_test
    {O : Set E} (hOc : IsCompact (closure O)) {u φ : E → ℝ} {A : ℝ≥0}
    (hu : LipschitzOnWith A u (closure O))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) :
    ∃ C : ℝ≥0, LipschitzWith C (fun x => φ x * Real.exp (-u x)) := by
  have hn := hu.neg
  have hcompact : IsCompact ((fun x => -u x) '' closure O) :=
    hOc.image_of_continuousOn hn.continuousOn
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn Real.continuous_exp.continuousOn
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hcompact
    Real.contDiff_exp.locallyLipschitz.locallyLipschitzOn
  apply compact_lipschitz_product ((hL.comp hn (mapsTo_image _ _)).mono subset_closure)
    (B := ⟨max B 0, le_max_right _ _⟩) ?_ hφ hφc hφO
  intro x hx
  exact (hB _ (mem_image_of_mem _ (subset_closure hx))).trans (le_max_left _ _)

end Poincare.Analysis.Elliptic
