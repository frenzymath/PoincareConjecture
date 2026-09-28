import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.PrincipalDynamics
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.StrongRecovery

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open ValueInitial

variable {n m : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)

private theorem tested_curve_integral {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (I : E →L[ℝ] H) {T : ℝ} (u w : ℝ → E)
    (hu : ContinuousOn u (Icc 0 T)) (hw : ContinuousOn w (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (w t) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Icc 0 T) (z : E) :
    inner ℝ (I z) (I (u t)) = inner ℝ (I z) (I (u 0)) +
      ∫ s in (0 : ℝ)..t, inner ℝ (I z) (I (w s)) := by
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hc : ContinuousOn (fun s => inner ℝ (I z) (I (u s))) (Icc 0 t) :=
    continuousOn_const.inner ((I.continuous.comp_continuousOn hu).mono hsub)
  have hdc : ContinuousOn (fun s => inner ℝ (I z) (I (w s))) (Icc 0 t) :=
    continuousOn_const.inner ((I.continuous.comp_continuousOn hw).mono hsub)
  have hderiv (s : ℝ) (hs : s ∈ Ioo 0 t) :
      HasDerivAt (fun y => inner ℝ (I z) (I (u y)))
        (inner ℝ (I z) (I (w s))) s := by
    have hsT : s ∈ Ioo 0 T := ⟨hs.1, hs.2.trans_le ht.2⟩
    exact (innerSL ℝ (I z)).hasFDerivAt.comp_hasDerivAt s
      (I.hasFDerivAt.comp_hasDerivAt s
        ((hd s (Ioo_subset_Icc_self hsT)).hasDerivAt
          (Icc_mem_nhds hsT.1 hsT.2)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hc hderiv
    (hdc.intervalIntegrable_of_Icc ht.1)]
  abel

private theorem tested_source_integral {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (I : E →L[ℝ] H) (L : ℝ → E → H) (Q : ℝ → E → E → ℝ)
    {r T : ℝ} (u w : ℝ → E)
    (hu : ContinuousOn u (Icc 0 T)) (hw : ContinuousOn w (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (w t) (Icc 0 T) t)
    (heq : ∀ t ∈ Icc 0 T, ∀ z, inner ℝ (I z) (I (w t)) =
      inner ℝ (I z) (L (r + t) (u t)) - Q (r + t) z (u t)) :
    ∀ t ∈ Icc 0 T, ∀ z, inner ℝ (I z) (I (u t)) = inner ℝ (I z) (I (u 0)) +
      ∫ s in (0 : ℝ)..t, inner ℝ (I z) (L (r + s) (u s)) - Q (r + s) z (u s) := by
  intro t ht z
  have hi : (∫ s in (0 : ℝ)..t, inner ℝ (I z) (I (w s))) =
      ∫ s in (0 : ℝ)..t, inner ℝ (I z) (L (r + s) (u s)) - Q (r + s) z (u s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact heq s ((Icc_subset_Icc le_rfl ht.2)
      (by simpa only [uIcc_of_le ht.1] using hs)) z
  rw [← hi]
  exact tested_curve_integral I u w hu hw hd ht z

private theorem tested_curve_derivative {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (I : E →L[ℝ] H) {T t : ℝ} {u : ℝ → E} {w : E}
    (hd : HasDerivWithinAt u w (Icc 0 T) t) (z : E) :
    HasDerivWithinAt (fun s => inner ℝ (I z) (I (u s))) (inner ℝ (I z) (I w))
      (Icc 0 T) t :=
  (innerSL ℝ (I z)).hasFDerivAt.comp_hasDerivWithinAt t
    (I.hasFDerivAt.comp_hasDerivWithinAt t hd)

private theorem tested_source_derivative {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (I : E →L[ℝ] H) (L : ℝ → E → H) (Q : ℝ → E → E → ℝ)
    {r T : ℝ} (u w : ℝ → E)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (w t) (Icc 0 T) t)
    (heq : ∀ t ∈ Icc 0 T, ∀ z, inner ℝ (I z) (I (w t)) =
      inner ℝ (I z) (L (r + t) (u t)) - Q (r + t) z (u t)) :
    ∀ t ∈ Icc 0 T, ∀ z,
      HasDerivWithinAt (fun s => inner ℝ (I z) (I (u s)))
        (inner ℝ (I z) (L (r + t) (u t)) - Q (r + t) z (u t)) (Icc 0 T) t := by
  intro t ht z
  exact (tested_curve_derivative I (hd t ht) z).congr_deriv (heq t ht z)

theorem principalValueHeat_of_continuous_form_derivative
    (K : Set X) (A : ℝ → Fin n → Fin n → 𝓢(X, ℝ))
    (L : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletValue K)) {r T : ℝ}
    (u w : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K))
    (hu : ContinuousOn u (Icc 0 T)) (hw : ContinuousOn w (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (w t) (Icc 0 T) t)
    (heq : ∀ t ∈ Icc 0 T, ∀ z : PiLp 2 (fun _ : Fin m => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) (w t)) =
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z) (L (r + t) (u t)) -
            principalVectorEnergy K (A (r + t)) z (u t)) :
    PrincipalValueHeat K A L r T (finiteHilbertMap (dirichletInclusion K) (u 0))
      u (fun t => finiteHilbertMap (dirichletInclusion K) (u t)) := by
  have hI := (finiteHilbertMap (V := dirichletForm K) (H := dirichletValue K)
    (m := m) (dirichletInclusion K)).continuous
  refine ⟨memLp_of_continuousOn_time hu, rfl, hI.comp_continuousOn hu,
    Filter.Eventually.of_forall (fun _ => rfl), ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact tested_source_derivative (finiteHilbertMap (dirichletInclusion K))
      (fun t => L t) (fun t => principalVectorEnergy K (A t)) u w hd heq t
      (Ioc_subset_Icc_self ht)
  · exact tested_source_integral (finiteHilbertMap (dirichletInclusion K))
      (fun t => L t) (fun t => principalVectorEnergy K (A t)) u w hu hw hd heq

end PoincareConjecture.M35.Uniqueness.Heat
