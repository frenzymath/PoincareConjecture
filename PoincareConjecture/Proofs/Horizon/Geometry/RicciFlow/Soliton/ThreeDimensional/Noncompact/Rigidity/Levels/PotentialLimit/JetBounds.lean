import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Eventual
import Mathlib.Analysis.Calculus.ContDiff.Bounds










noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 12

open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Q" => E →L[ℝ] ℝ
local notation "T" => E →L[ℝ] Q

theorem locallyEventuallyBoundedDerivatives_of_hessian_recurrence
    {Ω : Set E} {f : ℕ → E → ℝ}
    {A : ℕ → E → Q →L[ℝ] T} {B : ℕ → E → T}
    (hf : LocallyEventuallyContDiff Ω f)
    (hA : LocallyEventuallyContDiff Ω A) (hB : LocallyEventuallyContDiff Ω B)
    (hAbound : LocallyEventuallyBoundedDerivatives Ω A)
    (hBbound : LocallyEventuallyBoundedDerivatives Ω B)
    (hzero : ∀ K : Set E, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K, ‖f k x‖ ≤ C)
    (hone : ∀ K : Set E, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K, ‖fderiv ℝ (f k) x‖ ≤ C)
    (hrec : ∀ K : Set E, IsCompact K → K ⊆ Ω →
      ∀ᶠ k in atTop, ∀ x ∈ K,
        fderiv ℝ (fderiv ℝ (f k)) =ᶠ[𝓝 x]
          fun y => A k y (fderiv ℝ (f k) y) + B k y) :
    LocallyEventuallyBoundedDerivatives Ω f := by
  classical
  intro K hK hKΩ m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases m with _ | (_ | m)
    · simpa only [norm_iteratedFDeriv_zero] using hzero K hK hKΩ
    · simpa only [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] using
        hone K hK hKΩ
    · choose a ha using fun i : Fin (m + 1) => hAbound K hK hKΩ i
      choose d hd using fun i : Fin (m + 1) => ih (i + 1) (by omega)
      obtain ⟨b, hb⟩ := hBbound K hK hKΩ m
      let ev : (Q →L[ℝ] T) →L[ℝ] Q →L[ℝ] T := (ContinuousLinearMap.apply ℝ T).flip
      refine ⟨‖ev‖ * ∑ i : Fin (m + 1),
          (m.choose i : ℝ) * |a i| * |d ⟨m - i, by omega⟩| + b, ?_⟩
      have hAs : ∀ᶠ k in atTop, ∀ i : Fin (m + 1), ∀ x ∈ K,
          ‖iteratedFDeriv ℝ i (A k) x‖ ≤ a i := eventually_all.mpr ha
      have hds : ∀ᶠ k in atTop, ∀ i : Fin (m + 1), ∀ x ∈ K,
          ‖iteratedFDeriv ℝ (i + 1) (f k) x‖ ≤ d i := eventually_all.mpr hd
      filter_upwards [hf K hK hKΩ, hA K hK hKΩ, hB K hK hKΩ,
        hAs, hds, hb, hrec K hK hKΩ] with k hkf hkA hkB hka hkd hkb hkrec
      obtain ⟨Uf, hUf, hKUf, hfk⟩ := hkf
      obtain ⟨UA, hUA, hKUA, hAk⟩ := hkA
      obtain ⟨UB, hUB, hKUB, hBk⟩ := hkB
      let U := Uf ∩ UA ∩ UB
      have hU : IsOpen U := (hUf.inter hUA).inter hUB
      have hKsub : K ⊆ U := fun x hx => ⟨⟨hKUf hx, hKUA hx⟩, hKUB hx⟩
      have hfu : ContDiffOn ℝ ∞ (f k) U := hfk.mono (fun _ hx => hx.1.1)
      have hAu : ContDiffOn ℝ ∞ (A k) U := hAk.mono (fun _ hx => hx.1.2)
      have hBu : ContDiffOn ℝ ∞ (B k) U := hBk.mono (fun _ hx => hx.2)
      have hdu : ContDiffOn ℝ ∞ (fderiv ℝ (f k)) U :=
        hfu.fderiv_of_isOpen hU (by simp)
      intro x hx
      have hxU := hKsub hx
      have hm : (m : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
      have heq := ((hkrec x hx).iteratedFDeriv ℝ m).eq_of_nhds
      rw [← norm_iteratedFDeriv_fderiv, ← norm_iteratedFDeriv_fderiv, heq]
      change ‖iteratedFDeriv ℝ m ((fun y => A k y (fderiv ℝ (f k) y)) + B k) x‖ ≤ _
      rw [iteratedFDeriv_add_apply
          (((hAu.clm_apply hdu).contDiffAt (hU.mem_nhds hxU)).of_le hm)
          ((hBu.contDiffAt (hU.mem_nhds hxU)).of_le hm)]
      apply (norm_add_le _ _).trans
      apply add_le_add _ (hkb x hx)
      have hp := ev.norm_iteratedFDerivWithin_le_of_bilinear hAu hdu hU.uniqueDiffOn hxU hm
      simp only [iteratedFDerivWithin_of_isOpen _ hU hxU] at hp
      apply hp.trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg ev)
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_le_sum
      intro i hi
      have hAi := (hka i x hx).trans (le_abs_self _)
      have hdi := (hkd ⟨m - i, by omega⟩ x hx).trans (le_abs_self _)
      rw [norm_iteratedFDeriv_fderiv]
      gcongr

end Poincare.Analysis.Calculus
