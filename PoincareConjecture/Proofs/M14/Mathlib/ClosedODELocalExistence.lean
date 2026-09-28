import PoincareConjecture.Proofs.M14.Mathlib.ClosedODEBounds
import PoincareConjecture.Proofs.M14.Mathlib.ClosedPicardRange










set_option autoImplicit false

open Set Metric
open scoped ContDiff NNReal

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]





theorem closedODE_exists_local_family {a b t₀ : ℝ} (hab : a < b)
    {U : Set E} (hU : IsOpen U) (V : ℝ × E → E)
    (hV : ContDiffOn ℝ ∞ V (Icc a b ×ˢ U))
    (ht₀ : t₀ ∈ Icc a b) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ δ > (0 : ℝ), ∃ r > (0 : ℝ),
      let C := Icc (max a (t₀ - δ)) (min b (t₀ + δ))
      max a (t₀ - δ) < min b (t₀ + δ) ∧
      ∃ α : E × ℝ → E, ContinuousOn α (closedBall x₀ r ×ˢ C) ∧
        ∀ x ∈ closedBall x₀ r, α (x, t₀) = x ∧
          MapsTo (fun t => α (x, t)) C U ∧ ContDiffOn ℝ ∞ (fun t => α (x, t)) C ∧
          ∀ t ∈ C, HasDerivWithinAt (fun s => α (x, s)) (V (t, α (x, t))) C t := by
  obtain ⟨A, L, K, hA, hL, hAU, hnorm, hLip⟩ :=
    closedODE_exists_ball_bounds hab hU V hV hx₀
  have hA' : (0 : ℝ) < A := hA
  have hL' : (0 : ℝ) < L := hL
  let δ := (A : ℝ) / (2 * (L : ℝ))
  have hδ : 0 < δ := div_pos hA' (mul_pos (by norm_num) hL')
  let c := max a (t₀ - δ)
  let d := min b (t₀ + δ)
  have hcd : c < d := max_lt (lt_min hab (by linarith [ht₀.1]))
    (lt_min (by linarith [ht₀.2]) (by linarith))
  have htC : t₀ ∈ Icc c d :=
    ⟨max_le ht₀.1 (by linarith), le_min ht₀.2 (by linarith)⟩
  have hsub : Icc c d ⊆ Icc a b := fun t ht =>
    ⟨(le_max_left _ _).trans ht.1, ht.2.trans (min_le_left _ _)⟩
  have hmax : max (d - t₀) (t₀ - c) ≤ δ := by
    apply max_le
    · have hd : d ≤ t₀ + δ := min_le_right _ _
      linarith
    · have hc : t₀ - δ ≤ c := le_max_right _ _
      linarith
  have hscale : (L : ℝ) * δ = (A : ℝ) / 2 := by
    dsimp only [δ]
    field_simp
  let t₁ : Icc c d := ⟨t₀, htC⟩
  have hPL : IsPicardLindelof (fun t x => V (t, x)) t₁ x₀ A (A / 2) L K := by
    refine ⟨fun t ht => hLip t (hsub ht), ?_,
      fun t ht x hx => hnorm t (hsub ht) x hx, ?_⟩
    · intro x hx
      exact hV.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
        (fun t ht => ⟨hsub ht, hAU hx⟩)
    · change (L : ℝ) * max (d - t₀) (t₀ - c) ≤ (A : ℝ) - ((A / 2 : ℝ≥0) : ℝ)
      have hmul : (L : ℝ) * max (d - t₀) (t₀ - c) ≤ (A : ℝ) / 2 :=
        (mul_le_mul_of_nonneg_left hmax (show (0 : ℝ) ≤ (L : ℝ) from L.property)).trans_eq hscale
      simpa only [NNReal.coe_div, NNReal.coe_ofNat] using
        hmul.trans (show (A : ℝ) / 2 ≤ (A : ℝ) - (A : ℝ) / 2 by linarith)
  obtain ⟨α, hc, hα⟩ := exists_closedPicard_family_in_domain hcd hPL hU hAU
    (hV.mono (prod_mono hsub Subset.rfl))
  refine ⟨δ, hδ, ((A / 2 : ℝ≥0) : ℝ), ?_, hcd, α, hc, hα⟩
  simpa only [NNReal.coe_div, NNReal.coe_ofNat] using half_pos hA'

end PoincareConjecture.M14
