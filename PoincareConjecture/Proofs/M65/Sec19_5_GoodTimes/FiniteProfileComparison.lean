import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.WeightedGapBound
import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.WeightedProfileError









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} (F : RicciFlow 3 M (Icc a b))




theorem m65FiniteProfileComparison (compact : IsCompact (univ : Set M))
    {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) :
    ∃ G : ℝ, 0 < G ∧ ∃ U : ℝ, 0 < U ∧
      ∀ (f : ℝ → ℝ) (n : ℕ) (time : ℕ → ℝ) (good : Finset ℕ) (delta error : ℝ),
        (∀ t ∈ Icc a b, |f t| ≤ A) →
        (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |f t - f s| ≤ L * |t - s|) →
        time 0 = a → time n = b → (∀ i ≤ n, time i ∈ Icc a b) →
        (∀ i < n, time i ≤ time (i + 1)) → 0 ≤ error →
        (∀ i < n, i ∈ good → f (time (i + 1)) ≤
          m65RestartedAreaProfile F (time i) (f (time i)) (time (i + 1)) + error) →
        (∑ i ∈ Finset.range n, if i ∈ good then 0 else time (i + 1) - time i) ≤ delta →
        f b ≤ areaComparisonProfile F (f a) b +
          (G * delta + U * (n : ℝ) * error) / m65AreaWeight F b := by
  obtain ⟨G, hG, hgap⟩ := m65WeightedArea_uniformGapBound F compact hA hL
  obtain ⟨U, hU, _, _, hweight, _, _⟩ := m65AreaWeight_uniformBounds F compact
  refine ⟨G, hG, U, hU, ?_⟩
  intro f n time good delta error hbound hlip hstart hend htime hordered herror hgood hdelta
  let gap : ℕ → ℝ := fun i => if i ∈ good then 0 else time (i + 1) - time i
  have hstep (i : ℕ) (hi : i < n) :
      m65WeightedArea F f (time (i + 1)) - m65WeightedArea F f (time i) ≤
        G * gap i + U * error := by
    have hs := htime i hi.le
    have ht := htime (i + 1) (Nat.succ_le_of_lt hi)
    by_cases hg : i ∈ good
    · have hw := m65RestartedAreaProfile_weighted_comparison F (time i) (time (i + 1))
        (f a) (f (time i)) (f (time (i + 1))) error (hgood i hi hg)
      change m65AreaWeight F (time (i + 1)) *
          (f (time (i + 1)) - areaComparisonProfile F (f a) (time (i + 1))) ≤
        m65AreaWeight F (time i) * (f (time i) - areaComparisonProfile F (f a) (time i)) +
          m65AreaWeight F (time (i + 1)) * error at hw
      rw [← m65WeightedArea_profile_error F f (f a) (time (i + 1)),
        ← m65WeightedArea_profile_error F f (f a) (time i)] at hw
      have he := mul_le_mul_of_nonneg_right
        ((le_abs_self _).trans (hweight _ ht)) herror
      simp only [gap, if_pos hg, mul_zero, zero_add]
      linarith
    · have hw := (le_abs_self
        (m65WeightedArea F f (time (i + 1)) - m65WeightedArea F f (time i))).trans
          (hgap f hbound hlip _ hs _ ht)
      rw [abs_of_nonneg (sub_nonneg.mpr (hordered i hi))] at hw
      simp only [gap, if_neg hg]
      exact hw.trans (le_add_of_nonneg_right (mul_nonneg hU.le herror))
  have hsum : m65WeightedArea F f b - f a ≤ G * delta + U * (n : ℝ) * error := by
    calc
      _ = ∑ i ∈ Finset.range n,
          (m65WeightedArea F f (time (i + 1)) - m65WeightedArea F f (time i)) := by
        rw [Finset.sum_range_sub (fun i => m65WeightedArea F f (time i)),
          hstart, hend, m65WeightedArea_initial]
      _ ≤ ∑ i ∈ Finset.range n, (G * gap i + U * error) :=
        Finset.sum_le_sum (fun i hi => hstep i (Finset.mem_range.mp hi))
      _ = G * (∑ i ∈ Finset.range n, gap i) + U * (n : ℝ) * error := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hdelta hG.le) le_rfl
  rw [m65WeightedArea_profile_error] at hsum
  have hdivide : f b - areaComparisonProfile F (f a) b ≤
      (G * delta + U * (n : ℝ) * error) / m65AreaWeight F b :=
    (le_div_iff₀ (m65AreaWeight_pos F b)).mpr (by simpa only [mul_comm] using hsum)
  linarith

end PoincareConjecture
