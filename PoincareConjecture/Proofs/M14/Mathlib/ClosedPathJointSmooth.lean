import PoincareConjecture.Proofs.M14.Mathlib.ClosedPathEvaluation
import PoincareConjecture.Proofs.M14.Mathlib.ClosedPathMixedDerivative

set_option autoImplicit false

open Set
open scoped Topology ContDiff

namespace PoincareConjecture.M14

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {a b : ℝ}

theorem closedPath_timeJets_contDiff_nat (hab : a < b) (t₀ : Icc a b)
    {U : Set P} (hU : IsOpen U) (n : ℕ) (Φ : ℕ → P → C(Icc a b, F))
    (hΦ : ∀ j, ContDiffOn ℝ ∞ (Φ j) U)
    (ht : ∀ j, ∀ x ∈ U, ∀ r : Icc a b, HasDerivWithinAt
      (fun s => Φ j x (projIcc a b hab.le s)) (Φ (j + 1) x r) (Icc a b) r.val) :
    ContDiffOn ℝ n (closedPathEvaluation hab.le (Φ 0)) (U ×ˢ Icc a b) := by
  induction n generalizing Φ with
  | zero =>
    exact contDiffOn_zero.mpr ((continuousOn_closedPathEvaluation hab.le (hΦ 0).continuousOn).mono
      (prod_mono Subset.rfl (subset_univ _)))
  | succ n ih =>
    let D : P × ℝ → (P × ℝ) →L[ℝ] F := fun z =>
      (((ContinuousMap.evalCLM (R := ℝ) (projIcc a b hab.le z.2)).comp
        (fderiv ℝ (Φ 0) z.1)).coprod
          ((1 : ℝ →L[ℝ] ℝ).smulRight (closedPathEvaluation hab.le (Φ 1) z)))
    have hd (z : P × ℝ) (hz : z ∈ U ×ˢ Icc a b) :
        HasFDerivWithinAt (closedPathEvaluation hab.le (Φ 0)) (D z) (U ×ˢ Icc a b) z := by
      have h := hasFDerivWithinAt_closedPathEvaluation hab.le
        (((hΦ 0).contDiffAt (hU.mem_nhds hz.1)).differentiableAt (by simp)).hasFDerivAt
        ⟨z.2, hz.2⟩ (ht 0 z.1 hz.1 ⟨z.2, hz.2⟩)
      have hπ : projIcc a b hab.le z.2 = ⟨z.2, hz.2⟩ := projIcc_of_mem hab.le hz.2
      dsimp only [D, closedPathEvaluation]
      rw [hπ]
      exact h.mono (prod_mono (subset_univ _) Subset.rfl)
    simp only [Nat.cast_add, Nat.cast_one]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (hU.uniqueDiffOn.prod (uniqueDiffOn_Icc hab))).mpr
    refine ⟨by simp, D, ?_, hd⟩
    apply contDiffOn_clm_apply.mpr
    intro w
    let Ψ : ℕ → P → C(Icc a b, F) := fun j x => fderiv ℝ (Φ j) x w.1
    have hΨ (j : ℕ) : ContDiffOn ℝ ∞ (Ψ j) U :=
      ((hΦ j).fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
    have hΨt (j : ℕ) (x : P) (hx : x ∈ U) (r : Icc a b) : HasDerivWithinAt
        (fun s => Ψ j x (projIcc a b hab.le s)) (Ψ (j + 1) x r) (Icc a b) r.val :=
      closedPath_parameter_time_derivative t₀ hU (Φ j) (Φ (j + 1))
        ((hΦ j).differentiableOn (by simp)) ((hΦ (j + 1)).differentiableOn (by simp))
        (ht j) hx w.1 r
    have hparam := ih Ψ hΨ hΨt
    have htime := ih (fun j => Φ (j + 1)) (fun j => hΦ (j + 1)) (fun j => ht (j + 1))
    exact hparam.add (htime.const_smul w.2)

theorem closedPath_timeJets_contDiff (hab : a < b) (t₀ : Icc a b)
    {U : Set P} (hU : IsOpen U) (Φ : ℕ → P → C(Icc a b, F))
    (hΦ : ∀ j, ContDiffOn ℝ ∞ (Φ j) U)
    (ht : ∀ j, ∀ x ∈ U, ∀ r : Icc a b, HasDerivWithinAt
      (fun s => Φ j x (projIcc a b hab.le s)) (Φ (j + 1) x r) (Icc a b) r.val) :
    ContDiffOn ℝ ∞ (closedPathEvaluation hab.le (Φ 0)) (U ×ˢ Icc a b) :=
  contDiffOn_infty.mpr fun n => closedPath_timeJets_contDiff_nat hab t₀ hU n Φ hΦ ht

end PoincareConjecture.M14
