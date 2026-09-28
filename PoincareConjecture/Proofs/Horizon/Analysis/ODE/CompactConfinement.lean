import PoincareConjecture.Proofs.Horizon.Analysis.ODE.CompactTime









noncomputable section

namespace Poincare.ODE

open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]



theorem exists_solution_of_compact_confinement
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {F : E → E} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ K)
    {T : ℝ} (hT : 0 ≤ T)
    (hconf : ∀ t ∈ Icc 0 T, ∀ γ : ℝ → E, γ 0 = x →
      (∀ r ∈ Icc 0 t, γ r ∈ U ∧
        HasDerivWithinAt γ (F (γ r)) (Icc 0 t) r) → γ t ∈ K) :
    ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Icc 0 T, γ t ∈ U ∧ HasDerivWithinAt γ (F (γ t)) (Icc 0 T) t := by
  obtain ⟨δ, hδ, hlocal⟩ := exists_uniform_local_solutions hU hK hKU hF
  obtain ⟨N, hN⟩ := exists_nat_gt (T / δ)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg hT hδ.le) hN
  let d : ℝ := T / N
  let s : ℕ → ℝ := fun i => i * d
  have hd : 0 ≤ d := div_nonneg hT hNpos.le
  have hsmall : d < δ := by
    apply (div_lt_iff₀ hNpos).2
    have := (div_lt_iff₀ hδ).mp hN
    nlinarith
  have hs0 : s 0 = 0 := by simp [s]
  have hsN : s N = T := by dsimp [s, d]; field_simp
  have hsnonneg (i : ℕ) : 0 ≤ s i := mul_nonneg (Nat.cast_nonneg i) hd
  have hsstep (i : ℕ) : s (i + 1) = s i + d := by dsimp [s]; push_cast; ring
  have hsmono (i : ℕ) : s i ≤ s (i + 1) := by rw [hsstep]; linarith
  have hsle (i : ℕ) (hi : i ≤ N) : s i ≤ T := by
    rw [← hsN]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hd
  have hinterval : Icc 0 d ⊆ Ioo (-δ) δ :=
    fun t ht => ⟨by linarith [ht.1], ht.2.trans_lt hsmall⟩
  have aux : ∀ i, i ≤ N → ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Icc 0 (s i), γ t ∈ U ∧
        HasDerivWithinAt γ (F (γ t)) (Icc 0 (s i)) t := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨γ, hinit, hγ⟩ := hlocal x hx
      refine ⟨γ, hinit, ?_⟩
      intro t ht
      have ht0 : t = 0 := by rw [hs0] at ht; exact le_antisymm ht.2 ht.1
      subst t
      exact ⟨by simpa only [hinit] using hKU hx,
        (hγ 0 ⟨by linarith, hδ⟩).2.hasDerivWithinAt⟩
    | succ i ih =>
      intro hi
      obtain ⟨γ₁, hinit, hγ₁⟩ := ih (Nat.le_of_succ_le hi)
      have hjoinK := hconf (s i) ⟨hsnonneg i, hsle i (Nat.le_of_succ_le hi)⟩
        γ₁ hinit hγ₁
      obtain ⟨β, hβ0, hβ⟩ := hlocal (γ₁ (s i)) hjoinK
      let γ₂ : ℝ → E := fun t => β (t - s i)
      have hjoin : γ₂ (s i) = γ₁ (s i) := by simp only [γ₂, sub_self, hβ0]
      have hγ₂ : ∀ t ∈ Icc (s i) (s (i + 1)), γ₂ t ∈ U ∧
          HasDerivAt γ₂ (F (γ₂ t)) t := by
        intro t ht
        have hr : t - s i ∈ Icc 0 d := by
          rw [hsstep] at ht
          constructor <;> linarith [ht.1, ht.2]
        refine ⟨(hβ _ (hinterval hr)).1, ?_⟩
        simpa only [γ₂, one_smul, Function.comp_def, id_eq] using
          (hβ _ (hinterval hr)).2.scomp t ((hasDerivAt_id t).sub_const (s i))
      let γ : ℝ → E := fun t => if t ≤ s i then γ₁ t else γ₂ t
      have hγd := hasDerivWithinAt_glue (hsnonneg i) (hsmono i)
        (fun t ht => (hγ₁ t ht).2)
        (fun t ht => (hγ₂ t ht).2.hasDerivWithinAt) hjoin
      refine ⟨γ, by simpa only [γ, if_pos (hsnonneg i)] using hinit, ?_⟩
      intro t ht
      refine ⟨?_, hγd t ht⟩
      by_cases hti : t ≤ s i
      · simpa only [γ, if_pos hti] using (hγ₁ t ⟨ht.1, hti⟩).1
      · simpa only [γ, if_neg hti] using (hγ₂ t ⟨le_of_not_ge hti, ht.2⟩).1
  simpa only [hsN] using aux N le_rfl

end Poincare.ODE
