import PoincareConjecture.Proofs.M09.CompactActionBound
import PoincareConjecture.Proofs.M09.ExponentialCoercivity

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

theorem lExponentialFamily_minimizing_initial_bounded {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hL : LGeodesicTheory F T τmax) (p : M) (A : LExponentialFamily F T τmax p)
    (Q : Set (M × ℝ)) (hQ : IsCompact Q) (hQt : Q ⊆ Set.univ ×ˢ Set.Ioo 0 τmax) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ Z τ (hτ : 0 < τ) (hmax : τ < τmax),
      (A.gamma Z τ, τ) ∈ Q → IsMinimizingBackwardLPath F T 0 τ (A.path Z τ hτ hmax) →
        (F.metric T).tangentNorm p Z ≤ R := by
  rcases Q.eq_empty_or_nonempty with hzero | hnonempty
  · refine ⟨0, le_rfl, ?_⟩
    intro Z τ hτ hmax hmem
    exact (Set.notMem_empty _ (hzero ▸ hmem)).elim
  obtain ⟨za, hza, hmin⟩ := hQ.exists_isMinOn hnonempty continuous_snd.continuousOn
  obtain ⟨zb, hzb, hmax⟩ := hQ.exists_isMaxOn hnonempty continuous_snd.continuousOn
  have ha : 0 < za.2 := (hQt hza).2.1
  have hb : 0 < zb.2 := (hQt hzb).2.1
  have hbmax : zb.2 < τmax := (hQt hzb).2.2
  obtain ⟨D, hD, hDbound⟩ := exists_compact_minimizing_action_bound F hM04 T τmax
    hτmax hwindow hL p Q hQ hQt
  obtain ⟨B, C, hB, hC, hcoercive⟩ := exists_uniform_lExponentialFamily_action_coercive
    F hM04 T τmax hτmax hwindow hcurvature zb.2 hb hbmax
  let K := Real.exp (B * Real.sqrt zb.2) *
    (2 * D + 4 * C * (Real.sqrt zb.2) ^ 3 + Real.sqrt zb.2)
  refine ⟨Real.sqrt (K / Real.sqrt za.2), Real.sqrt_nonneg _, ?_⟩
  intro Z τ hτ hτmax hmem hPmin
  have hta : za.2 ≤ τ := hmin hmem
  have htb : τ ≤ zb.2 := hmax hmem
  have haction : A.action Z τ ≤ D := by
    have he := hDbound (A.gamma Z τ, τ) hmem (A.path Z τ hτ hτmax)
      ((congrFun (A.path_eq Z τ hτ hτmax) 0).trans (A.gamma_at_zero Z))
      (congrFun (A.path_eq Z τ hτ hτmax) τ) hPmin
    simpa only [LExponentialFamily.action, A.path_eq] using he
  have he : 0 ≤ (F.metric T).inner p Z Z := by
    rcases eq_or_ne Z 0 with rfl | hne
    · simp
    · exact ((F.metric T).pos p Z hne).le
  have hs0 : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg _
  have hsb : Real.sqrt τ ≤ Real.sqrt zb.2 := Real.sqrt_le_sqrt htb
  have hsa : Real.sqrt za.2 ≤ Real.sqrt τ := Real.sqrt_le_sqrt hta
  have hcub : (Real.sqrt τ) ^ 3 ≤ (Real.sqrt zb.2) ^ 3 := pow_le_pow_left₀ hs0 hsb 3
  have hf : 2 * D + 4 * C * (Real.sqrt τ) ^ 3 + Real.sqrt τ ≤
      2 * D + 4 * C * (Real.sqrt zb.2) ^ 3 + Real.sqrt zb.2 := by
    have hmul : 4 * C * (Real.sqrt τ) ^ 3 ≤ 4 * C * (Real.sqrt zb.2) ^ 3 :=
      mul_le_mul_of_nonneg_left hcub (mul_nonneg (by norm_num) hC)
    linarith
  have hexp : Real.exp (B * Real.sqrt τ) ≤ Real.exp (B * Real.sqrt zb.2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsb hB.le)
  have hnonneg : 0 ≤ 2 * D + 4 * C * (Real.sqrt τ) ^ 3 + Real.sqrt τ := by positivity
  have hupper : Real.sqrt τ * (4 * (F.metric T).inner p Z Z + 1) ≤ K := by
    calc
      _ ≤ Real.exp (B * Real.sqrt τ) *
          (2 * A.action Z τ + 4 * C * (Real.sqrt τ) ^ 3 + Real.sqrt τ) :=
        hcoercive p A Z τ hτ htb
      _ ≤ Real.exp (B * Real.sqrt τ) *
          (2 * D + 4 * C * (Real.sqrt τ) ^ 3 + Real.sqrt τ) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        linarith
      _ ≤ K := mul_le_mul hexp hf hnonneg (Real.exp_pos _).le
  have hsmall : Real.sqrt za.2 * (F.metric T).inner p Z Z ≤ K := by
    have hmul := mul_le_mul_of_nonneg_right hsa he
    have henergy : Real.sqrt τ * (F.metric T).inner p Z Z ≤
        Real.sqrt τ * (4 * (F.metric T).inner p Z Z + 1) := by
      apply mul_le_mul_of_nonneg_left _ hs0
      linarith
    exact hmul.trans (henergy.trans hupper)
  apply Real.sqrt_le_sqrt
  exact (le_div_iff₀ (Real.sqrt_pos.mpr ha)).mpr (by simpa only [mul_comm] using hsmall)

end PoincareConjecture.Proofs.M09
