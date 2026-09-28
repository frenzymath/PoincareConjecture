import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.TangentCone.Prod









set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

universe u v




theorem contDiffOn_spatial_deriv_of_uniqueDiffOn
    {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set P} (hS : UniqueDiffOn ℝ S) {q : P → ℝ → E}
    {m n : ℕ∞ω} (hmn : m + 1 ≤ n)
    (hq : ContDiffOn ℝ n (Function.uncurry q) (S ×ˢ univ)) :
    ContDiffOn ℝ m (fun z : P × ℝ => deriv (q z.1) z.2) (S ×ˢ univ) := by
  have hone : (1 : ℕ∞ω) ≤ n :=
    (le_add_of_nonneg_left (show (0 : ℕ∞ω) ≤ m from bot_le)).trans hmn
  have hn : n ≠ 0 := ne_of_gt ((show (0 : ℕ∞ω) < 1 by decide).trans_le hone)
  have hd := (hq.fderivWithin (hS.prod uniqueDiffOn_univ) hmn).clm_apply
    (contDiffOn_const (c := (0, (1 : ℝ))))
  apply hd.congr
  intro z hz
  have hline : HasDerivAt (fun y : ℝ => (z.1, y)) (0, 1) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  have hmaps : ∀ᶠ y in 𝓝 z.2, (z.1, y) ∈ S ×ˢ (univ : Set ℝ) :=
    Eventually.of_forall fun _ => ⟨hz.1, mem_univ _⟩
  exact (((hq.differentiableOn hn) z hz).hasFDerivWithinAt.comp_hasDerivAt
    z.2 hline hmaps).deriv
