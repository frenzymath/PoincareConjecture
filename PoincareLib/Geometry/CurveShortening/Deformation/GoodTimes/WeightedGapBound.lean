import PoincareLib.Geometry.CurveShortening.Deformation.GoodTimes.WeightBounds

/-!
# Uniform weighted-area increments on arbitrary time gaps

Claims 19.26-19.27, Morgan--Tian pp. 457-459, using the actual area
boundedness and time-Lipschitz constants from Claim 19.23.
See M65 derivation 18 for the scalar-sign repair.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} (F : RicciFlow 3 M (Icc a b))

/-- One positive weighted gap constant works for every function with the
given actual area and Lipschitz bounds; Claims 19.26-19.27, pp. 457-459. -/
theorem m65WeightedArea_uniformGapBound (compact : IsCompact (univ : Set M))
    {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) :
    ∃ G : ℝ, 0 < G ∧ ∀ f : ℝ → ℝ,
      (∀ t ∈ Icc a b, |f t| ≤ A) →
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |f t - f s| ≤ L * |t - s|) →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        |m65WeightedArea F f t - m65WeightedArea F f s| ≤ G * |t - s| := by
  obtain ⟨U, hU, D, hD, hweight, hdiff, hint⟩ := m65AreaWeight_uniformBounds F compact
  let G := U * L + D * A + 2 * Real.pi * U
  have hG : 0 < G := by dsimp [G]; positivity
  refine ⟨G, hG, ?_⟩
  intro f hbound hlip s hs t ht
  have hproduct : |m65AreaWeight F t * f t - m65AreaWeight F s * f s| ≤
      (U * L + D * A) * |t - s| := by
    have hsplit : m65AreaWeight F t * f t - m65AreaWeight F s * f s =
        m65AreaWeight F t * (f t - f s) + (m65AreaWeight F t - m65AreaWeight F s) * f s := by
      ring
    rw [hsplit]
    calc
      _ ≤ |m65AreaWeight F t * (f t - f s)| +
          |(m65AreaWeight F t - m65AreaWeight F s) * f s| := abs_add_le _ _
      _ = |m65AreaWeight F t| * |f t - f s| +
          |m65AreaWeight F t - m65AreaWeight F s| * |f s| := by rw [abs_mul, abs_mul]
      _ ≤ U * (L * |t - s|) + (D * |t - s|) * A :=
        add_le_add (mul_le_mul (hweight t ht) (hlip s hs t ht) (abs_nonneg _) hU.le)
          (mul_le_mul (hdiff s hs t ht) (hbound s hs) (abs_nonneg _)
            (mul_nonneg hD.le (abs_nonneg _)))
      _ = _ := by ring
  have ha : a ∈ Icc a b := ⟨le_rfl, hs.1.trans hs.2⟩
  have hcontinuous := m65AreaWeight_continuousOn F compact
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    ((hcontinuous.mono (uIcc_subset_Icc ha hs)).intervalIntegrable (μ := volume))
    ((hcontinuous.mono (uIcc_subset_Icc hs ht)).intervalIntegrable (μ := volume))
  have hsplit : m65WeightedArea F f t - m65WeightedArea F f s =
      (m65AreaWeight F t * f t - m65AreaWeight F s * f s) +
        2 * Real.pi * ∫ r in s..t, m65AreaWeight F r := by
    unfold m65WeightedArea
    rw [← hadd]
    ring
  rw [hsplit]
  calc
    _ ≤ |m65AreaWeight F t * f t - m65AreaWeight F s * f s| +
        |2 * Real.pi * ∫ r in s..t, m65AreaWeight F r| := abs_add_le _ _
    _ = |m65AreaWeight F t * f t - m65AreaWeight F s * f s| +
        (2 * Real.pi) * |∫ r in s..t, m65AreaWeight F r| := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)]
    _ ≤ (U * L + D * A) * |t - s| + (2 * Real.pi) * (U * |t - s|) :=
      add_le_add hproduct (mul_le_mul_of_nonneg_left (hint s hs t ht)
        (mul_nonneg (by norm_num) Real.pi_pos.le))
    _ = G * |t - s| := by dsimp [G]; ring

end PoincareMT
