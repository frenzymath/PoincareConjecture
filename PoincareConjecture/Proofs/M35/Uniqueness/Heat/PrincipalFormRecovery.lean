import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormTraceRecovery
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.SlabTimeRegularity

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

theorem principalVectorForm_coercive {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) {ell : ℝ}
    (hEll : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (u : PiLp 2 (fun _ : Fin m => dirichletForm K)) :
    min 1 ell * ‖u‖ ^ 2 ≤ inner ℝ u (finiteHilbertMap (principalFormOperator K A) u) +
      ‖finiteHilbertMap (dirichletInclusion K) u‖ ^ 2 := by
  have hnorm : ‖u‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq u, PiLp.inner_apply]
    simp only [real_inner_self_eq_norm_sq]
  have hinorm : ‖finiteHilbertMap (dirichletInclusion K) u‖ ^ 2 =
      ∑ i, ‖dirichletInclusion K (u i)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (finiteHilbertMap (dirichletInclusion K) u),
      PiLp.inner_apply]
    simp only [finiteHilbertMap_apply, real_inner_self_eq_norm_sq]
  have hsum : (∑ i, min 1 ell * ‖u i‖ ^ 2) ≤
      ∑ i, (principalEnergy K A (u i) (u i) + ‖dirichletInclusion K (u i)‖ ^ 2) := by
    apply Finset.sum_le_sum
    intro i _
    have hc := principalFormPairing_coercive hK A hEll (u i)
    simpa only [principalFormPairing, real_inner_self_eq_norm_sq, add_comm] using hc
  simpa only [hnorm, hinorm, principalVectorEnergy_pairing, principalVectorEnergy,
    Finset.mul_sum, Finset.sum_add_distrib] using hsum

theorem exists_principalValueHeat_smooth_form
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
    (hsol : PrincipalValueHeat K A L 0 B u₀ v U) :
    ∃ w : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K),
      (∀ t ∈ Ioo 0 B, ContDiffAt ℝ ∞ w t) ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 B), w t = v t) ∧
      (∀ t ∈ Ioo 0 B, finiteHilbertMap (dirichletInclusion K) (w t) = U t) ∧
      (∀ t ∈ Ioo 0 B, ∀ z : PiLp 2 (fun _ : Fin m => dirichletForm K),
        inner ℝ (finiteHilbertMap (dirichletInclusion K) z) (deriv U t) =
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z) (L t (w t)) -
            principalVectorEnergy K (A t) z (w t)) := by
  let I : PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletValue K) :=
    finiteHilbertMap (dirichletInclusion K)
  let P : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletForm K) :=
    fun t => finiteHilbertMap (principalFormOperator K (A t))
  have hbound : ∃ C : ℝ, ∀ t ∈ Icc 0 B, ‖L t‖ ≤ C := by
    exact isCompact_Icc.exists_bound_of_continuousOn hLc.continuousOn
  obtain ⟨C, hCb⟩ := hbound
  have hL : ∀ t ∈ Ioo 0 B, ‖L t‖ ≤ C :=
    fun t ht => hCb t (Ioo_subset_Icc_self ht)
  have hPc : ContDiffOn ℝ ∞ P (Ioo 0 B) := by
    simpa only [P, Function.comp_def, finiteHilbertMapOperator_apply] using
      ((finiteHilbertMapOperator (E := dirichletForm K) (F := dirichletForm K)
        (m := m)).contDiff.comp_contDiffOn hAc).mono Ioo_subset_Icc_self
  have hU : ∀ t ∈ Ioo 0 B, ContDiffAt ℝ ∞ U t :=
    fun t ht => contDiffAt_principalValueHeat_slab hK A hell hA hEll hAc L hLc hsol (t := t) ht
  have hw : ∀ᵐ t ∂timeMeasure B, ∀ z : PiLp 2 (fun _ : Fin m => dirichletForm K),
      HasDerivWithinAt (fun s => inner ℝ (I z) (U s))
        (inner ℝ (I z) (L t (v t)) - inner ℝ z (P t (v t))) (Icc 0 B) t := by
    simpa only [I, P, principalVectorEnergy_pairing, zero_add] using hsol.2.2.2.2.1
  have hPb : ∀ t ∈ Ioo 0 B, ∀ u : PiLp 2 (fun _ : Fin m => dirichletForm K),
      min 1 ell * ‖u‖ ^ 2 ≤ inner ℝ u (P t u) + ‖I u‖ ^ 2 :=
    fun t ht u => principalVectorForm_coercive (m := m) hK.isClosed (A t)
      (hEll t (Ioo_subset_Icc_self ht)) u
  have hrec := exists_smooth_form_trace I P L
    (B := B) (c := min 1 ell) (C := C) (v := v) (U := U)
    (lt_min zero_lt_one hell) hL hPb hPc (hLc.mono Ioo_subset_Icc_self) hU hsol.2.2.2.1 hw
  simpa only [I, P, principalVectorEnergy_pairing] using hrec

end PoincareConjecture.M35.Uniqueness.Heat
