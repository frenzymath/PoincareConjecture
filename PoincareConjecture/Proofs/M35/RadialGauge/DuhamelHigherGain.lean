import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelThirdJets
import PoincareConjecture.Proofs.M35.RadialGauge.HeatUnweighted









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

universe u

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))



theorem heatDuhamel_iteratedFDeriv_gain (k : ℕ)
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → V → F} {t C : ℝ} (ht : 0 ≤ t) (hC : 0 ≤ C)
    (hfm : StronglyMeasurable (fun p : Icc 0 t × V => f p.1.1 p.2))
    (hf : ∀ s ∈ Icc 0 t, ContDiff ℝ ∞ (f s))
    (hbound : ∀ j : ℕ, ∃ B : ℝ, ∀ s ∈ Icc 0 t, ∀ x,
      ‖iteratedFDeriv ℝ j (f s) x‖ ≤ B)
    (hk : ∀ s ∈ Icc 0 t, ∀ x, ‖iteratedFDeriv ℝ k (f s) x‖ ≤ C)
    (x : V) :
    ‖iteratedFDeriv ℝ (k + 1) (heatDuhamel f t) x‖ ≤
      C * (2 * gaussianFirstMoment (n + 1) * Real.sqrt t) := by
  induction k generalizing F with
  | zero =>
      let g := slabSourceExtension t f
      have hgm : StronglyMeasurable (Function.uncurry g) :=
        slabSourceExtension_stronglyMeasurable hfm
      have hgeq (s : ℝ) (hs : s ∈ Icc 0 t) : g s = f s :=
        slabSourceExtension_of_mem hs f
      have hgs (s : ℝ) (hs : s ∈ Icc 0 t) : ContDiff ℝ ∞ (g s) := by
        rw [hgeq s hs]
        exact hf s hs
      have hgb (s : ℝ) (hs : s ∈ Icc 0 t) (y : V) : ‖g s y‖ ≤ C := by
        rw [hgeq s hs]
        simpa only [norm_iteratedFDeriv_zero] using hk s hs y
      obtain ⟨D, hD⟩ := hbound 1
      have hd := heatDuhamel_hasFDerivAt_of_bounds hC ht hgm
        (fun s hs => (hgs s hs).continuous)
        (fun s hs => (hgs s ⟨hs.1, hs.2.le⟩).continuous_fderiv (by simp))
        (fun s hs y => ((hgs s ⟨hs.1, hs.2.le⟩).differentiable (by simp) y).hasFDerivAt)
        (fun s hs => ⟨D, fun y => by
          rw [hgeq s ⟨hs.1, hs.2.le⟩]
          simpa only [norm_iteratedFDeriv_one] using hD s ⟨hs.1, hs.2.le⟩ y⟩)
        hgb x
      rw [Nat.zero_add, norm_iteratedFDeriv_one,
        ← heatDuhamel_slabSourceExtension ⟨ht, le_rfl⟩ f, hd.fderiv]
      exact heatDuhamelGradient_norm_le hC ht
        (fun s hs => (hgs s hs).continuous) hgb x
  | succ k ih =>
      have hdm := spatial_fderiv_stronglyMeasurable (f := fun s : Icc 0 t => f s.1)
        hfm (fun s => (hf s.1 s.2).differentiable (by simp))
      have hds (s : ℝ) (hs : s ∈ Icc 0 t) :=
        (contDiff_infty_iff_fderiv.mp (hf s hs)).2
      have hdb : ∀ j : ℕ, ∃ B : ℝ, ∀ s ∈ Icc 0 t, ∀ y,
          ‖iteratedFDeriv ℝ j (fderiv ℝ (f s)) y‖ ≤ B := by
        intro j
        obtain ⟨B, hB⟩ := hbound (j + 1)
        exact ⟨B, fun s hs y => by
          simpa only [norm_iteratedFDeriv_fderiv] using hB s hs y⟩
      rw [← norm_iteratedFDeriv_fderiv,
        heatDuhamel_fderiv_eq_of_slab ht hfm hf hbound]
      exact ih hdm hds hdb (fun s hs y => by
        simpa only [norm_iteratedFDeriv_fderiv] using hk s hs y)

end PoincareConjecture.M35.RadialGauge
