import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.FiniteProfileComparison









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} (F : RicciFlow 3 M (Icc a b))




theorem m65FiniteProfileTolerance (compact : IsCompact (univ : Set M))
    {A L eta : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ n : ℕ, ∃ error : ℝ, 0 < error ∧
      ∀ (f : ℝ → ℝ) (time : ℕ → ℝ) (good : Finset ℕ),
        (∀ t ∈ Icc a b, |f t| ≤ A) →
        (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |f t - f s| ≤ L * |t - s|) →
        time 0 = a → time n = b → (∀ i ≤ n, time i ∈ Icc a b) →
        (∀ i < n, time i ≤ time (i + 1)) →
        (∀ i < n, i ∈ good → f (time (i + 1)) ≤
          m65RestartedAreaProfile F (time i) (f (time i)) (time (i + 1)) + error) →
        (∑ i ∈ Finset.range n, if i ∈ good then 0 else time (i + 1) - time i) ≤ delta →
        f b < areaComparisonProfile F (f a) b + eta := by
  obtain ⟨G, hG, U, hU, hcompare⟩ := m65FiniteProfileComparison F compact hA hL
  let W := m65AreaWeight F b
  have hW : 0 < W := m65AreaWeight_pos F b
  let delta := eta * W / (4 * G)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  refine ⟨delta, hdelta, ?_⟩
  intro n
  let error := eta * W / (4 * U * ((n : ℝ) + 1))
  have herror : 0 < error := by dsimp [error]; positivity
  refine ⟨error, herror, ?_⟩
  intro f time good hbound hlip hstart hend htime hordered hgood hgap
  have h := hcompare f n time good delta error hbound hlip hstart hend htime hordered
    herror.le hgood hgap
  have hbudget : (G * delta + U * (n : ℝ) * error) / W ≤ eta / 2 := by
    calc
      _ ≤ (G * delta + U * ((n : ℝ) + 1) * error) / W := by
        apply div_le_div_of_nonneg_right _ hW.le
        apply add_le_add le_rfl
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) hU.le) herror.le
      _ = eta / 2 := by
        dsimp [delta, error]
        have hn : (n : ℝ) + 1 ≠ 0 := by positivity
        field_simp
        ring
  change f b ≤ areaComparisonProfile F (f a) b +
    (G * delta + U * (n : ℝ) * error) / W at h
  linarith

end PoincareConjecture
