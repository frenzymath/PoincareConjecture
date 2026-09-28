import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FiniteHilbertOperator
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.StrongHeatEquivalent

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

theorem exists_finite_equivalent_strong_heat
    (I : H →L[ℝ] X) (hIc : IsCompactOperator I) (hId : DenseRange I)
    (hIi : Function.Injective I) (e : W ≃L[ℝ] H)
    (hJn : ‖I.comp e.toContinuousLinearMap‖ ≤ 1)
    {b : ℝ} (hb : 0 < b) (P : ℝ → H →L[ℝ] H)
    (hP : ContDiffOn ℝ 1 P (Icc 0 b))
    (B : ℝ → H → H → ℝ) (hPB : ∀ t u v, inner ℝ u (P t v) = B t u v)
    (hB : ∀ u v : W, inner ℝ u v =
      inner ℝ (I (e u)) (I (e v)) + B 0 (e u) (e v))
    (L : ℝ → PiLp 2 (fun _ : Fin m => H) →L[ℝ] PiLp 2 (fun _ : Fin m => X))
    (hL : ContDiffOn ℝ 1 L (Icc 0 b)) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ T < b ∧
      ∀ u₀ w₀ : PiLp 2 (fun _ : Fin m => H),
      (∀ z : PiLp 2 (fun _ : Fin m => H),
        inner ℝ (finiteHilbertMap I z) (finiteHilbertMap I w₀) =
          inner ℝ (finiteHilbertMap I z) (L 0 u₀) - ∑ i, B 0 (z i) (u₀ i)) →
      ∃ (u : ℝ → PiLp 2 (fun _ : Fin m => H))
        (Z : ℝ → PiLp 2 (fun _ : Fin m => X)),
        u 0 = u₀ ∧ Z 0 = finiteHilbertMap I w₀ ∧
        ContinuousOn u (Icc 0 T) ∧ ContinuousOn Z (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt
          (fun s => finiteHilbertMap I (u s)) (Z t) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, ∀ z : PiLp 2 (fun _ : Fin m => H),
          inner ℝ (finiteHilbertMap I z) (Z t) =
            inner ℝ (finiteHilbertMap I z) (L t (u t)) - ∑ i, B t (z i) (u t i)) ∧
        ∃ w : ℝ → PiLp 2 (fun _ : Fin m => H),
          MemLp w 2 (SpectralHeatNative.timeMeasure T) ∧
          ∀ᵐ t ∂SpectralHeatNative.timeMeasure T,
            HasDerivAt u (w t) t ∧ finiteHilbertMap I (w t) = Z t := by
  let IV := finiteHilbertMap (m := m) I
  let E := finiteHilbertEquiv (m := m) e
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
  let R : ℝ → PiLp 2 (fun _ : Fin m => H) →L[ℝ] PiLp 2 (fun _ : Fin m => H) :=
    fun t => finiteHilbertMapOperator (P 0 - P t)
  have hR : ContDiffOn ℝ 1 R (Icc 0 b) :=
    (finiteHilbertMapOperator (m := m) (E := H) (F := H)).contDiff.comp_contDiffOn
      ((contDiffOn_const (c := P 0)).sub hP)
  have hR0 : R 0 = 0 := by
    dsimp only [R]
    rw [sub_self, map_zero]
  have hp (t : ℝ) (u z : PiLp 2 (fun _ : Fin m => H)) :
      inner ℝ z (R t u) = BV z u - ∑ i, B t (z i) (u i) := by
    simp only [R, BV, finiteHilbertMapOperator_apply, PiLp.inner_apply,
      finiteHilbertMap_apply, sub_apply, inner_sub_right, Finset.sum_sub_distrib, hPB]
  obtain ⟨T, hT, hT1, hTb, hsolve⟩ := exists_equivalent_strong_initial_heat IV
    (finiteHilbertMap_compact _ hIc) (finiteHilbertMap_denseRange _ hId)
    (finiteHilbertMap_injective _ hIi) E hIn BV hBV hb R hR hR0 L hL
  refine ⟨T, hT, hT1, hTb, ?_⟩
  intro u₀ w₀ hcompat
  have hinit (z : PiLp 2 (fun _ : Fin m => H)) :
      inner ℝ (IV z) (IV w₀) = inner ℝ z (R 0 u₀) +
        inner ℝ (IV z) (L 0 u₀) - BV z u₀ := by
    rw [hp, sub_self, zero_add]
    exact hcompat z
  obtain ⟨u, Z, hu0, hZ0, hu, hZ, hd, heq, hjet⟩ := hsolve _ _ hinit
  refine ⟨u, Z, hu0, hZ0, hu, hZ, hd, ?_, hjet⟩
  intro t ht z
  rw [heq t ht z, hp]
  ring

end PoincareConjecture.M35.Uniqueness.Heat
