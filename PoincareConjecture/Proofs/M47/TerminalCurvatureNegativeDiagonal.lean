import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset









set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M47



theorem terminalCurvature_exists_negative_diagonal
    (tau : ℕ → ℝ) (htau : ∀ k, 0 < tau k)
    (Available : ℕ → ℕ → Prop) (P : ℕ → ℕ → ℝ → Prop)
    (hmod : ∀ k i, Available k i → ∃ delta : ℝ, 0 < delta ∧
      ∀ s ∈ Icc (-tau k) 0, |s| < delta → P k i s) :
    ∃ s : ℕ → ℝ, (∀ k, s k ∈ Ioo (-tau k) 0) ∧
      Tendsto s atTop (𝓝 0) ∧
      ∀ k i, i ≤ k → Available k i → P k i (s k) := by
  classical
  have hguarded (k i : ℕ) : ∃ delta : ℝ, 0 < delta ∧
      (Available k i → ∀ s ∈ Icc (-tau k) 0, |s| < delta → P k i s) := by
    by_cases hi : Available k i
    · obtain ⟨delta, hd, hds⟩ := hmod k i hi
      exact ⟨delta, hd, fun _ => hds⟩
    · exact ⟨1, zero_lt_one, fun h => (hi h).elim⟩
  choose d hd hds using hguarded
  let b (k : ℕ) : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i : Fin (k + 1) => d k i)
  have hb (k : ℕ) : 0 < b k :=
    (Finset.lt_inf'_iff _).mpr (fun i _ => hd k i)
  let a (k : ℕ) : ℝ := min (tau k / 2) (min (b k / 2) (1 / ((k : ℝ) + 1)))
  have ha (k : ℕ) : 0 < a k :=
    lt_min (half_pos (htau k)) (lt_min (half_pos (hb k)) (by positivity))
  have hata (k : ℕ) : a k < tau k :=
    (min_le_left _ _).trans_lt (half_lt_self (htau k))
  have hab (k : ℕ) : a k < b k :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self (hb k))
  have han (k : ℕ) : a k ≤ 1 / ((k : ℝ) + 1) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hzero : Tendsto a atTop (𝓝 0) :=
    squeeze_zero (fun k => (ha k).le) han tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨fun k => -a k, fun k => ⟨neg_lt_neg (hata k), neg_neg_of_pos (ha k)⟩,
    by simpa only [neg_zero] using hzero.neg, ?_⟩
  intro k i hik hi
  apply hds k i hi (-a k) ⟨(neg_lt_neg (hata k)).le, (neg_neg_of_pos (ha k)).le⟩
  rw [abs_neg, abs_of_pos (ha k)]
  exact (hab k).trans_le (Finset.inf'_le _ (Finset.mem_univ (⟨i, by omega⟩ : Fin (k + 1))))



theorem terminalCurvature_negative_diagonal_uniform_limit
    {Z : Type*} {Y : ℕ → Type*} [∀ i, PseudoMetricSpace (Y i)]
    (K : ℕ → Set Z) (tau : ℕ → ℝ) (htau : ∀ k, 0 < tau k)
    (Available : ℕ → ℕ → Prop) (hAvailable : ∀ i, ∀ᶠ k in atTop, Available k i)
    (f : ∀ (_ : ℕ), ∀ i : ℕ, ℝ → Z → Y i) (limit : ∀ i, Z → Y i)
    (hlimit : ∀ i, TendstoUniformlyOn (fun k => f k i 0) (limit i) atTop (K i))
    (hmod : ∀ k i, Available k i → ∀ rho : ℝ, 0 < rho →
      ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ Icc (-tau k) 0, |s| < delta →
        ∀ z ∈ K i, dist (f k i s z) (f k i 0 z) < rho) :
    ∃ s : ℕ → ℝ, (∀ k, s k ∈ Ioo (-tau k) 0) ∧ Tendsto s atTop (𝓝 0) ∧
      ∀ i, TendstoUniformlyOn (fun k => f k i (s k)) (limit i) atTop (K i) := by
  let P := fun k i s => ∀ z ∈ K i,
    dist (f k i s z) (f k i 0 z) < 1 / ((k : ℝ) + 1)
  have hm (k i : ℕ) (hi : Available k i) : ∃ delta : ℝ, 0 < delta ∧
      ∀ s ∈ Icc (-tau k) 0, |s| < delta → P k i s :=
    hmod k i hi _ (by positivity)
  obtain ⟨s, hs, hzero, hrows⟩ := terminalCurvature_exists_negative_diagonal
    tau htau Available P hm
  refine ⟨s, hs, hzero, ?_⟩
  intro i
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro epsilon hepsilon
  have herror : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < epsilon / 2 :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Iio_mem_nhds (half_pos hepsilon))
  filter_upwards [hAvailable i, eventually_ge_atTop i, herror,
      (Metric.tendstoUniformlyOn_iff.mp (hlimit i)) (epsilon / 2) (half_pos hepsilon)]
    with k hk hi herr hlim z hz
  have hrow := hrows k i hi hk z hz
  calc
    dist (limit i z) (f k i (s k) z) ≤
        dist (limit i z) (f k i 0 z) + dist (f k i 0 z) (f k i (s k) z) :=
      dist_triangle _ _ _
    _ < epsilon / 2 + epsilon / 2 :=
      add_lt_add (hlim z hz) (by simpa only [dist_comm] using hrow.trans herr)
    _ = epsilon := by ring

end PoincareConjecture.M47
