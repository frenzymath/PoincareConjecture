import PoincareConjecture.Proofs.Horizon.Analysis.Approximation.RegularizedMinimum

set_option autoImplicit false

open Set
open scoped ContDiff

namespace Poincare

noncomputable def finiteRegularizedMin (δ : ℝ) (hδ : 0 < δ) :
    (n : ℕ) → (Fin (n + 1) → ℝ) → ℝ
  | 0, f => f 0
  | n + 1, f => regularizedMin δ hδ (f 0) (finiteRegularizedMin δ hδ n (Fin.tail f))

theorem contDiff_finiteRegularizedMin (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    ContDiff ℝ ∞ (finiteRegularizedMin δ hδ n) := by
  induction n with
  | zero => exact contDiff_apply ℝ ℝ 0
  | succ n ih =>
    exact (contDiff_regularizedMin δ hδ).comp
      ((contDiff_apply ℝ ℝ 0).prodMk (ih.comp
        (contDiff_pi.mpr fun i => contDiff_apply ℝ ℝ i.succ)))

theorem finiteRegularizedMin_le (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (f : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : finiteRegularizedMin δ hδ n f ≤ f i := by
  induction n with
  | zero => simp only [finiteRegularizedMin, Fin.fin_one_eq_zero i, le_refl]
  | succ n ih =>
    have h := regularizedMin_le_min δ hδ (f 0) (finiteRegularizedMin δ hδ n (Fin.tail f))
    refine Fin.cases (h.trans (min_le_left _ _)) (fun i => ?_) i
    exact h.trans ((min_le_right _ _).trans (ih (Fin.tail f) i))

theorem finiteRegularizedMin_le_iInf (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (f : Fin (n + 1) → ℝ) : finiteRegularizedMin δ hδ n f ≤ ⨅ i, f i :=
  le_ciInf (finiteRegularizedMin_le δ hδ n f)

theorem sub_le_finiteRegularizedMin (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (f : Fin (n + 1) → ℝ) {c : ℝ} (hc : ∀ i, c ≤ f i) :
    c - n * δ / 2 ≤ finiteRegularizedMin δ hδ n f := by
  induction n with
  | zero => simpa only [finiteRegularizedMin, Nat.cast_zero, zero_mul, zero_div, sub_zero] using hc 0
  | succ n ih =>
    have htail := ih (Fin.tail f) (fun i => hc i.succ)
    have hhead : c - n * δ / 2 ≤ f 0 := by
      have hn : 0 ≤ (n : ℝ) * δ / 2 := by positivity
      linarith [hc 0]
    have hm := le_min hhead htail
    have hs := min_sub_le_regularizedMin δ hδ (f 0)
      (finiteRegularizedMin δ hδ n (Fin.tail f))
    change c - (n + 1 : ℕ) * δ / 2 ≤ _
    push_cast
    change c - ((n : ℝ) + 1) * δ / 2 ≤
      regularizedMin δ hδ (f 0) (finiteRegularizedMin δ hδ n (Fin.tail f))
    linarith

theorem iInf_sub_le_finiteRegularizedMin (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (f : Fin (n + 1) → ℝ) :
    (⨅ i, f i) - n * δ / 2 ≤ finiteRegularizedMin δ hδ n f :=
  sub_le_finiteRegularizedMin δ hδ n f (ciInf_le (Finite.bddBelow_range f))

theorem monotone_finiteRegularizedMin (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    Monotone (finiteRegularizedMin δ hδ n) := by
  induction n with
  | zero => exact fun _ _ h => h 0
  | succ n ih =>
    intro f g h
    exact ((monotone_regularizedMin_left δ hδ _) (h 0)).trans
      ((monotone_regularizedMin_right δ hδ _) (ih (fun i => h i.succ)))

theorem finiteRegularizedMin_add (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (f : Fin (n + 1) → ℝ) (t : ℝ) :
    finiteRegularizedMin δ hδ n (fun i => f i + t) = finiteRegularizedMin δ hδ n f + t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change regularizedMin δ hδ (f 0 + t)
      (finiteRegularizedMin δ hδ n (fun i => f i.succ + t)) = _
    rw [ih, regularizedMin_add]
    rfl

theorem concaveOn_finiteRegularizedMin (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    ConcaveOn ℝ univ (finiteRegularizedMin δ hδ n) := by
  induction n with
  | zero => exact ⟨convex_univ, fun _ _ _ _ _ _ _ _ _ => le_rfl⟩
  | succ n ih =>
    refine ⟨convex_univ, ?_⟩
    intro f hf g hg a b ha hb hab
    have htail := ih.2 (mem_univ (Fin.tail f)) (mem_univ (Fin.tail g)) ha hb hab
    have hbin := (concaveOn_regularizedMin δ hδ).2
      (mem_univ (f 0, finiteRegularizedMin δ hδ n (Fin.tail f)))
      (mem_univ (g 0, finiteRegularizedMin δ hδ n (Fin.tail g))) ha hb hab
    apply hbin.trans
    exact (monotone_regularizedMin_right δ hδ _) htail

end Poincare
