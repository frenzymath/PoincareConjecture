import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalTimeRegularity
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TimeRestriction
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.UniformStep









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative ValueInitial

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem contDiffAt_principalValueHeat_slab
    {K : Set V} (hK : IsCompact K) (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    {ell B : ℝ} (hell : 0 < ell)
    (hA : ∀ r ∈ Icc 0 B, ∀ i j x, A r i j x = A r j i x)
    (hEll : ∀ r ∈ Icc 0 B, ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A r i j x * ξ i * ξ j)
    (hAc : ContDiffOn ℝ ∞ (fun r => principalFormOperator K (A r)) (Icc 0 B))
    (L : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletValue K)) (hLc : ContDiffOn ℝ ∞ L (Icc 0 B))
    {u₀ : PiLp 2 (fun _ : Fin m => dirichletValue K)}
    {v : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K)}
    {U : ℝ → PiLp 2 (fun _ : Fin m => dirichletValue K)}
    (hsol : PrincipalValueHeat K A L 0 B u₀ v U)
    {t : ℝ} (ht : t ∈ Ioo 0 B) : ContDiffAt ℝ ∞ U t := by
  let P : ℝ → dirichletForm K →L[ℝ] dirichletForm K :=
    fun r => principalFormOperator K (A r)
  let c := min 1 ell
  have hc : 0 < c := lt_min zero_lt_one hell
  let M := c⁻¹
  have hM : 0 < M := inv_pos.mpr hc
  have hM1 : 1 ≤ M := (one_le_inv₀ hc).mpr (min_le_left _ _)
  have hscale : 1 ≤ min 1 ell * M ^ 2 := by
    calc
      1 = c * M := (mul_inv_cancel₀ hc.ne').symm
      _ ≤ (c * M) * M := le_mul_of_one_le_right (by positivity) hM1
      _ = min 1 ell * M ^ 2 := by dsimp only [c]; ring
  obtain ⟨q, C, τ, hq, hC, hτ, _, hPb, hLb, hsmall⟩ :=
    exists_uniform_mixed_step hM P hAc.continuousOn L hLc.continuousOn
  let d := min τ (min (t / 2) ((B - t) / 2))
  have hd : 0 < d := lt_min hτ (lt_min (half_pos ht.1) (half_pos (sub_pos.mpr ht.2)))
  have hdτ : d ≤ τ := min_le_left _ _
  have hdt : d ≤ t / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdB : d ≤ (B - t) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  let S := t - d
  have hS : 0 ≤ S := by dsimp only [S]; linarith only [hdt, ht.1]
  have hSB : S + 2 * d ≤ B := by dsimp only [S]; linarith only [hdB, hd]
  have hS0 : S ∈ Icc 0 B := ⟨hS, by linarith only [hSB, hd]⟩
  have hshift : MapsTo (fun r : ℝ => S + r) (Icc 0 (2 * d)) (Icc 0 B) := by
    intro r hr
    constructor <;> linarith only [hS, hSB, hr.1, hr.2]
  have hA' : ContDiffOn ℝ ∞ (fun r => principalFormOperator K (A (S + r)))
      (Icc 0 (2 * d)) :=
    hAc.comp (contDiffOn_const.add contDiffOn_id) hshift
  have hL' : ContDiffOn ℝ ∞ (fun r => L (S + r)) (Icc 0 (2 * d)) :=
    hLc.comp (contDiffOn_const.add contDiffOn_id) hshift
  have hsub : Icc (0 : ℝ) d ⊆ Icc 0 (2 * d) :=
    Icc_subset_Icc le_rfl (by linarith only [hd])
  have hAb : ∀ r ∈ Icc 0 d, ‖P (S + 0) - P (S + r)‖ ≤ q := by
    intro r hr
    have hdist : |S - (S + r)| ≤ τ := by
      rw [show S - (S + r) = -r by ring, abs_neg, abs_of_nonneg hr.1]
      exact hr.2.trans hdτ
    simpa only [add_zero] using hPb S hS0 (S + r) (hshift (hsub hr)) hdist
  have hLc' : ∀ r ∈ Icc 0 d, ‖L (S + r)‖ ≤ C :=
    fun r hr => hLb (S + r) (hshift (hsub hr))
  have hsym : ∀ i j x, A (S + 0) i j x = A (S + 0) j i x := by
    simpa only [add_zero] using hA S hS0
  have hell' : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A (S + 0) i j x * ξ i * ξ j := by
    simpa only [add_zero] using hEll S hS0
  have hPr : ContinuousOn (fun r => principalFormOperator K (A (0 + r))) (Icc 0 B) := by
    simpa only [zero_add] using hAc.continuousOn
  have hLr : ContinuousOn (fun r => L (0 + r)) (Icc 0 B) := by
    simpa only [zero_add] using hLc.continuousOn
  have hs0 := principalValueHeat_restrict K A L hS (by positivity : 0 ≤ 2 * d) hSB
    hPr hLr hsol
  have hs : PrincipalValueHeat K (fun r => A (S + r)) (fun r => L (S + r)) 0 (2 * d)
      (U S) (fun r => v (S + r)) (fun r => U (S + r)) := by
    simpa only [zero_add] using hs0
  have hlocal := contDiffAt_principalValueHeat hK (fun r => A (S + r)) hell hd le_rfl
    hM.le hq.le hC.le hscale hsym hell' hA' hAb (fun r => L (S + r)) hL' hLc'
    (hsmall d ⟨hd.le, hdτ⟩) hs ⟨hd, le_rfl⟩
  have hpoint : t - S = d := by dsimp only [S]; ring
  have hlocal' : ContDiffAt ℝ ∞ (fun r => U (S + r)) (t - S) := hpoint.symm ▸ hlocal
  have hlin : ContDiffAt ℝ ∞ (fun r : ℝ => r - S) t := contDiffAt_id.sub contDiffAt_const
  have hcomp := hlocal'.comp (f := fun r : ℝ => r - S) t hlin
  have heq : (fun r : ℝ => U (S + (r - S))) = U := by
    funext r
    congr 1
    ring
  simpa only [Function.comp_def, heq] using hcomp

end PoincareConjecture.M35.Uniqueness.Heat
