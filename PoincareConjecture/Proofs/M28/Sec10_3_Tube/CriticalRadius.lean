import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic










set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M28.tube



def eventuallyRadiusBound {X : ℕ → Type u} (d q : ∀ k, X k → ℝ) (r : ℝ) : Prop :=
  ∃ K : ℝ, ∀ᶠ k in atTop, ∀ x : X k, d k x < r → q k x ≤ K

theorem eventuallyRadiusBound_mono {X : ℕ → Type u} {d q : ∀ k, X k → ℝ}
    {r s : ℝ} (h : eventuallyRadiusBound d q s) (hrs : r ≤ s) :
    eventuallyRadiusBound d q r := by
  obtain ⟨K, hK⟩ := h
  exact ⟨K, hK.mono fun k hk x hx => hk x (hx.trans_le hrs)⟩



theorem exists_critical_radius_witnesses {X : ℕ → Type u}
    (d q : ∀ k, X k → ℝ) {r₀ L : ℝ}
    (hr₀ : 0 < r₀) (hlocal : eventuallyRadiusBound d q r₀)
    (hhigh : ∀ K : ℝ, ∃ᶠ k in atTop, ∃ x : X k, d k x < L ∧ K < q k x) :
    ∃ A : ℝ, 0 < A ∧ A ≤ L ∧
      (∀ r < A, eventuallyRadiusBound d q r) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : ∀ j, X (φ j),
        ∀ j, d (φ j) (x j) < A + 1 / ((j : ℝ) + 1) ∧ (j : ℝ) < q (φ j) (x j) := by
  let S : Set ℝ := {r | eventuallyRadiusBound d q r}
  have hS : S.Nonempty := ⟨r₀, hlocal⟩
  have hupper : ∀ r ∈ S, r ≤ L := by
    intro r hr
    by_contra hle
    have hLr : L < r := lt_of_not_ge hle
    obtain ⟨K, hK⟩ := hr
    obtain ⟨k, ⟨x, hx, hqx⟩, hk⟩ := ((hhigh K).and_eventually hK).exists
    exact (not_lt_of_ge (hk x (hx.trans hLr))) hqx
  have hb : BddAbove S := ⟨L, hupper⟩
  let A := sSup S
  have hApos : 0 < A := hr₀.trans_le (le_csSup hb hlocal)
  have hAL : A ≤ L := csSup_le hS hupper
  have hinterior : ∀ r < A, eventuallyRadiusBound d q r := by
    intro r hr
    obtain ⟨s, hs, hrs⟩ := exists_lt_of_lt_csSup hS hr
    exact eventuallyRadiusBound_mono hs hrs.le
  have hwitness (r K : ℝ) (hr : A < r) :
      ∃ᶠ k in atTop, ∃ x : X k, d k x < r ∧ K < q k x := by
    by_contra hnot
    have htail := not_frequently.mp hnot
    have hbound : eventuallyRadiusBound d q r := by
      refine ⟨K, htail.mono ?_⟩
      intro k hk x hx
      exact le_of_not_gt (fun hq => hk ⟨x, hx, hq⟩)
    exact (not_le_of_gt hr) (le_csSup hb hbound)
  have hfreq (j : ℕ) : ∃ᶠ k in atTop, ∃ x : X k,
      d k x < A + 1 / ((j : ℝ) + 1) ∧ (j : ℝ) < q k x :=
    hwitness _ _ (lt_add_of_pos_right A (by positivity))
  obtain ⟨φ, hφ, hx⟩ := extraction_forall_of_frequently hfreq
  choose x hx using hx
  exact ⟨A, hApos, hAL, hinterior, φ, hφ, x, hx⟩




theorem critical_radius_preserved_by_subsequence {X : ℕ → Type u}
    (d q : ∀ k, X k → ℝ) {A : ℝ} (hA : 0 < A)
    (hinterior : ∀ r < A, eventuallyRadiusBound d q r)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (x : ∀ j, X (φ j))
    (hx : ∀ j, d (φ j) (x j) < A + 1 / ((j : ℝ) + 1) ∧
      (j : ℝ) < q (φ j) (x j))
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    sSup {r : ℝ | eventuallyRadiusBound
      (fun k => d (φ (ψ k))) (fun k => q (φ (ψ k))) r} = A := by
  let S : Set ℝ := {r | eventuallyRadiusBound
    (fun k => d (φ (ψ k))) (fun k => q (φ (ψ k))) r}
  have hin (r : ℝ) (hr : r < A) : r ∈ S := by
    obtain ⟨K, hK⟩ := hinterior r hr
    exact ⟨K, (hφ.comp hψ).tendsto_atTop.eventually hK⟩
  have hne : S.Nonempty := ⟨A / 2, hin _ (by linarith)⟩
  have hupper : ∀ r ∈ S, r ≤ A := by
    intro r hr
    by_contra hle
    have hAr : A < r := lt_of_not_ge hle
    obtain ⟨K, hK⟩ := hr
    have hsmall : ∀ᶠ k in atTop, A + 1 / ((ψ k : ℝ) + 1) < r := by
      have ht := ((tendsto_const_nhds (x := A)).add
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hψ.tendsto_atTop))
      have ht' : Tendsto (fun k => A + 1 / ((ψ k : ℝ) + 1)) atTop (𝓝 A) := by
        simpa only [add_zero, Function.comp_apply] using ht
      exact ht'.eventually (gt_mem_nhds hAr)
    have hlarge : ∀ᶠ k in atTop, K < (ψ k : ℝ) :=
      (tendsto_natCast_atTop_atTop.comp hψ.tendsto_atTop).eventually (eventually_gt_atTop K)
    obtain ⟨k, hk, hs, hl⟩ := (hK.and (hsmall.and hlarge)).exists
    exact (not_lt_of_ge (hk (x (ψ k)) ((hx (ψ k)).1.trans hs)))
      (hl.trans (hx (ψ k)).2)
  apply le_antisymm
  · exact csSup_le hne hupper
  · apply le_of_forall_lt
    intro r hr
    obtain ⟨s, hrs, hsA⟩ := exists_between hr
    exact hrs.trans_le (le_csSup ⟨A, hupper⟩ (hin s hsA))

end PoincareConjecture.M28.tube
