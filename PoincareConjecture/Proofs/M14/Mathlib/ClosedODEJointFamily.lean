import PoincareConjecture.Proofs.M14.Mathlib.ClosedODETimeJets
import PoincareConjecture.Proofs.M14.Mathlib.ClosedODEPathFamily

set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem closedODE_exists_joint_family {a b : ℝ} (hab : a < b) (t₀ : Icc a b)
    {U : Set E} (hU : IsOpen U) (f : ℝ × E → E)
    (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ U)) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ c d : ℝ, ∃ t₁ : Icc c d,
      c < d ∧ a ≤ c ∧ d ≤ b ∧ t₁.val = t₀.val ∧ Icc c d ∈ 𝓝[Icc a b] t₀.val ∧
      ∃ ρ > (0 : ℝ), ∃ α : E × ℝ → E,
        ContDiffOn ℝ ∞ α (ball x₀ ρ ×ˢ Icc c d) ∧ ∀ x ∈ ball x₀ ρ,
          α (x, t₁.val) = x ∧ ∀ s ∈ Icc c d,
            α (x, s) ∈ U ∧ HasDerivWithinAt (fun r => α (x, r))
              (f (s, α (x, s))) (Icc c d) s := by
  obtain ⟨R, hR, g, hRU, hg, hgf⟩ := exists_closedTime_state_extension hU f hf hx₀
  have hballU : ball x₀ R ⊆ U := ball_subset_closedBall.trans hRU
  obtain ⟨c, d, t₁, hcd, hac, hdb, hi, hnear, ρ, hρ, Φ, hΦ, hdata⟩ :=
    closedODE_exists_smooth_path_family hab t₀ isOpen_ball f
      (hf.mono (prod_mono Subset.rfl hballU)) (mem_ball_self hR)
  have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc hac hdb
  have hg' : ContDiffOn ℝ ∞ g (Icc c d ×ˢ univ) := hg.mono (prod_mono hsub Subset.rfl)
  let α := closedPathEvaluation hcd.le Φ
  have hsm : ContDiffOn ℝ ∞ α (ball x₀ ρ ×ˢ Icc c d) := by
    apply closedODEFamily_joint_contDiff hcd t₁ isOpen_ball g hg' Φ hΦ
    intro x hx s
    rw [hgf ⟨hsub s.property, ball_subset_closedBall ((hdata x hx).2.1 s)⟩]
    exact (hdata x hx).2.2.2 s
  have heval (x : E) (s : Icc c d) : α (x, s.val) = Φ x s := by
    dsimp only [α, closedPathEvaluation]
    rw [projIcc_of_mem hcd.le s.property]
  refine ⟨c, d, t₁, hcd, hac, hdb, hi, hnear, ρ, hρ, α, hsm, ?_⟩
  intro x hx
  refine ⟨(heval x t₁).trans (hdata x hx).1, ?_⟩
  intro s hs
  have hs' := heval x ⟨s, hs⟩
  refine ⟨hs'.symm ▸ hballU ((hdata x hx).2.1 ⟨s, hs⟩), ?_⟩
  rw [hs']
  exact (hdata x hx).2.2.2 ⟨s, hs⟩

end PoincareConjecture.M14
