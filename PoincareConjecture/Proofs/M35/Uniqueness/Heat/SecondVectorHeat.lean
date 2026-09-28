import PoincareConjecture.Proofs.M35.Uniqueness.Heat.SecondEquivalentHeat
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FiniteHilbertOperator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {W H X : Type*} {m : ℕ}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [SeparableSpace X]

theorem exists_finite_equivalent_second_heat
    (I : H →L[ℝ] X) (hIc : IsCompactOperator I) (hId : DenseRange I)
    (hIi : Function.Injective I) (e : W ≃L[ℝ] H)
    (hJn : ‖I.comp e.toContinuousLinearMap‖ ≤ 1)
    {b : ℝ} (hb : 0 < b) (P P₁ P₂ : ℝ → H →L[ℝ] H)
    (hP : ContDiffOn ℝ 1 P (Icc 0 b)) (hP₁ : ContDiffOn ℝ 1 P₁ (Icc 0 b))
    (hP₂ : ContinuousOn P₂ (Icc 0 b))
    (hPd : ∀ t ∈ Ioo 0 b, HasDerivAt P (P₁ t) t)
    (hP₁d : ∀ t ∈ Ioo 0 b, HasDerivAt P₁ (P₂ t) t)
    (B B₁ : ℝ → H → H → ℝ)
    (hPB : ∀ t u v, inner ℝ u (P t v) = B t u v)
    (hP₁B : ∀ t u v, inner ℝ u (P₁ t v) = B₁ t u v)
    (hB : ∀ u v : W, inner ℝ u v =
      inner ℝ (I (e u)) (I (e v)) + B 0 (e u) (e v))
    (L L₁ L₂ : ℝ → PiLp 2 (fun _ : Fin m => H) →L[ℝ] PiLp 2 (fun _ : Fin m => X))
    (hL : ContDiffOn ℝ 1 L (Icc 0 b)) (hL₁ : ContDiffOn ℝ 1 L₁ (Icc 0 b))
    (hL₂ : ContinuousOn L₂ (Icc 0 b))
    (hLd : ∀ t ∈ Ioo 0 b, HasDerivAt L (L₁ t) t)
    (hL₁d : ∀ t ∈ Ioo 0 b, HasDerivAt L₁ (L₂ t) t) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ T < b ∧
      ∀ u₀ w₀ z₀ : PiLp 2 (fun _ : Fin m => H),
      (∀ z : PiLp 2 (fun _ : Fin m => H),
        inner ℝ (finiteHilbertMap I z) (finiteHilbertMap I w₀) =
          inner ℝ (finiteHilbertMap I z) (L 0 u₀) - ∑ i, B 0 (z i) (u₀ i)) →
      (∀ z : PiLp 2 (fun _ : Fin m => H),
        inner ℝ (finiteHilbertMap I z) (finiteHilbertMap I z₀) =
          inner ℝ (finiteHilbertMap I z) (L 0 w₀) - (∑ i, B 0 (z i) (w₀ i)) +
            inner ℝ (finiteHilbertMap I z) (L₁ 0 u₀) - ∑ i, B₁ 0 (z i) (u₀ i)) →
      ∃ u w : ℝ → PiLp 2 (fun _ : Fin m => H), u 0 = u₀ ∧ w 0 = w₀ ∧
        ContinuousOn u (Icc 0 T) ∧ ContinuousOn w (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt u (w t) (Icc 0 T) t) ∧
        ∀ t ∈ Icc 0 T, ∀ z : PiLp 2 (fun _ : Fin m => H),
          inner ℝ (finiteHilbertMap I z) (finiteHilbertMap I (w t)) =
            inner ℝ (finiteHilbertMap I z) (L t (u t)) - ∑ i, B t (z i) (u t i) := by
  let IV := finiteHilbertMap (m := m) I
  let E := finiteHilbertEquiv (m := m) e
  let M := finiteHilbertMapOperator (m := m) (E := H) (F := H)
  have hIn : ‖IV.comp E.toContinuousLinearMap‖ ≤ 1 := by
    change ‖(finiteHilbertMap I).comp (finiteHilbertMap e.toContinuousLinearMap)‖ ≤ 1
    rw [← finiteHilbertMap_comp]
    exact (norm_finiteHilbertMap_le _).trans hJn
  let BV := fun u v : PiLp 2 (fun _ : Fin m => H) => ∑ i, B 0 (u i) (v i)
  have hBV (u v : PiLp 2 (fun _ : Fin m => W)) :
      inner ℝ u v = inner ℝ (IV (E u)) (IV (E v)) + BV (E u) (E v) := by
    simp only [PiLp.inner_apply, IV, E, BV, finiteHilbertMap_apply, finiteHilbertEquiv_apply]
    simp_rw [hB]
    exact Finset.sum_add_distrib
  let R := fun t => M (P 0 - P t)
  let R₁ := fun t => M (-P₁ t)
  let R₂ := fun t => M (-P₂ t)
  have hR : ContDiffOn ℝ 1 R (Icc 0 b) :=
    M.contDiff.comp_contDiffOn (contDiffOn_const.sub hP)
  have hR0 : R 0 = 0 := by simp only [R, sub_self, map_zero]
  have hR₁ : ContDiffOn ℝ 1 R₁ (Icc 0 b) := M.contDiff.comp_contDiffOn hP₁.neg
  have hR₂ : ContinuousOn R₂ (Icc 0 b) := M.continuous.comp_continuousOn hP₂.neg
  have hRd (t : ℝ) (ht : t ∈ Ioo 0 b) : HasDerivAt R (R₁ t) t := by
    simpa only [R, R₁, zero_sub, Function.comp_def, Pi.sub_def] using!
      M.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t (P 0)).sub (hPd t ht))
  have hR₁d (t : ℝ) (ht : t ∈ Ioo 0 b) : HasDerivAt R₁ (R₂ t) t :=
    M.hasFDerivAt.comp_hasDerivAt t (hP₁d t ht).neg
  have hp (t : ℝ) (u z : PiLp 2 (fun _ : Fin m => H)) :
      inner ℝ z (R t u) = BV z u - ∑ i, B t (z i) (u i) := by
    simp only [R, M, BV, finiteHilbertMapOperator_apply, PiLp.inner_apply,
      finiteHilbertMap_apply, sub_apply, inner_sub_right, Finset.sum_sub_distrib, hPB]
  have hp₁ (t : ℝ) (u z : PiLp 2 (fun _ : Fin m => H)) :
      inner ℝ z (R₁ t u) = -∑ i, B₁ t (z i) (u i) := by
    simp only [R₁, M, finiteHilbertMapOperator_apply, PiLp.inner_apply,
      finiteHilbertMap_apply, neg_apply, inner_neg_right, Finset.sum_neg_distrib, hP₁B]
  obtain ⟨T, hT, hT1, hTb, hsolve⟩ := exists_equivalent_second_initial_heat IV
    (finiteHilbertMap_compact _ hIc) (finiteHilbertMap_denseRange _ hId)
    (finiteHilbertMap_injective _ hIi) E hIn BV hBV hb
    R R₁ R₂ hR hR0 hR₁ hR₂ hRd hR₁d L L₁ L₂ hL hL₁ hL₂ hLd hL₁d
  refine ⟨T, hT, hT1, hTb, ?_⟩
  intro u₀ w₀ z₀ hcompat hcompat₁
  have hc₀ (z : PiLp 2 (fun _ : Fin m => H)) : inner ℝ (IV z) (IV w₀) =
      inner ℝ z (R 0 u₀) + inner ℝ (IV z) (L 0 u₀) - BV z u₀ := by
    rw [hp, sub_self, zero_add]
    exact hcompat z
  have hc₁ (z : PiLp 2 (fun _ : Fin m => H)) : inner ℝ (IV z) (IV z₀) =
      inner ℝ z (R 0 w₀) + inner ℝ (IV z) (L 0 w₀) - BV z w₀ +
        inner ℝ z (R₁ 0 u₀) + inner ℝ (IV z) (L₁ 0 u₀) := by
    rw [hp, hp₁, sub_self, zero_add, hcompat₁ z]
    ring
  obtain ⟨u, w, hu0, hw0, hu, hw, hd, he⟩ := hsolve u₀ w₀ z₀ hc₀ hc₁
  refine ⟨u, w, hu0, hw0, hu, hw, hd, ?_⟩
  intro t ht z
  rw [he t ht z, hp]
  ring

end PoincareConjecture.M35.Uniqueness.Heat
