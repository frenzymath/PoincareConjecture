import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.VectorInitial
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalResponse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat.ValueInitial

open SpectralHeatNative

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem exists_principal_vector_value_initial_heat
    {K : Set V} (hK : IsCompact K) (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    {ell T M q C : ℝ} (hell : 0 < ell) (hT : 0 ≤ T)
    (hM : 0 ≤ M) (hq : 0 ≤ q) (hC : 0 ≤ C) (hscale : 1 ≤ min 1 ell * M ^ 2)
    (hA : ∀ i j x, A 0 i j x = A 0 j i x)
    (hEll : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A 0 i j x * ξ i * ξ j)
    (hAc : ContinuousOn (fun t => principalFormOperator K (A t)) (Icc 0 T))
    (hAb : ∀ t ∈ Icc 0 T,
      ‖principalFormOperator K (A 0) - principalFormOperator K (A t)‖ ≤ q)
    (L : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletValue K))
    (hLc : ContinuousOn L (Icc 0 T)) (hLb : ∀ t ∈ Icc 0 T, ‖L t‖ ≤ C)
    (hsmall : (T + 1) * (M * (q * M)) +
      (Real.sqrt T * (Real.sqrt T + 1)) * (C * M) < 1)
    (u₀ : PiLp 2 (fun _ : Fin m => dirichletValue K)) :
    ∃ (v : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K))
      (U : ℝ → PiLp 2 (fun _ : Fin m => dirichletValue K)),
      MemLp v 2 (timeMeasure T) ∧ U 0 = u₀ ∧ ContinuousOn U (Icc 0 T) ∧
      (∀ᵐ t ∂timeMeasure T, finiteHilbertMap (dirichletInclusion K) (v t) = U t) ∧
      (∀ᵐ t ∂timeMeasure T, ∀ w : PiLp 2 (fun _ : Fin m => dirichletForm K),
        HasDerivWithinAt (fun s => inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (U s))
          (inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (L t (v t)) -
            principalVectorEnergy K (A t) w (v t)) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, ∀ w : PiLp 2 (fun _ : Fin m => dirichletForm K),
        inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (U t) =
          inner ℝ (finiteHilbertMap (dirichletInclusion K) w) u₀ +
          ∫ s in (0 : ℝ)..t, inner ℝ (finiteHilbertMap (dirichletInclusion K) w)
            (L s (v s)) - principalVectorEnergy K (A s) w (v s)) := by
  let Q := weightedCore hK.isClosed (A 0) hell hA hEll
  have hQc := weightedCore_continuous hK.isClosed (A 0) hell hA hEll
  have hQb := weightedCore_bounded hK.isClosed (A 0) hell hA hEll
  let : NormedAddCommGroup (WeightedForm K) := Q.toNormedAddCommGroupOfTopology hQc hQb
  let : InnerProductSpace ℝ (WeightedForm K) := InnerProductSpace.ofCoreOfTopology Q hQc hQb
  let e : WeightedForm K ≃L[ℝ] dirichletForm K :=
    { LinearEquiv.refl ℝ (dirichletForm K) with
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }
  let eu : WeightedForm K ≃ᵤ dirichletForm K :=
    { e.toEquiv with
      uniformContinuous_toFun := e.toContinuousLinearMap.uniformContinuous
      uniformContinuous_invFun := e.symm.toContinuousLinearMap.uniformContinuous }
  let : CompleteSpace (WeightedForm K) := eu.completeSpace_iff.mpr inferInstance
  let J : WeightedForm K →L[ℝ] dirichletValue K :=
    (dirichletInclusion K).comp e.toContinuousLinearMap
  have hJn : ‖J‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    have hE : 0 ≤ principalEnergy K (A 0) (e u) (e u) :=
      (mul_nonneg hell.le (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans
        (principalEnergy_coercive hK.isClosed (A 0) hEll (e u))
    have hs : ‖J u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq u]
      change ‖dirichletInclusion K (e u)‖ ^ 2 ≤ principalFormPairing K (A 0) (e u) (e u)
      simp only [principalFormPairing, real_inner_self_eq_norm_sq]
      linarith only [hE]
    simpa only [one_mul] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs
  have he : ‖e.toContinuousLinearMap‖ ≤ M := by
    apply ContinuousLinearMap.opNorm_le_bound _ hM
    intro u
    have hc := principalFormPairing_coercive hK.isClosed (A 0) hEll (e u)
    have hnorm : principalFormPairing K (A 0) (e u) (e u) = ‖u‖ ^ 2 :=
      real_inner_self_eq_norm_sq u
    rw [hnorm] at hc
    have h1 := mul_le_mul_of_nonneg_right hscale (sq_nonneg ‖e u‖)
    have h2 := mul_le_mul_of_nonneg_left hc (sq_nonneg M)
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg u))).mp
    change ‖e u‖ ^ 2 ≤ (M * ‖u‖) ^ 2
    nlinarith only [h1, h2]
  exact exists_finite_equivalent_value_initial_heat (dirichletInclusion K)
    (isCompactOperator_dirichletInclusion hK) (dirichletInclusion_denseRange K)
    (dirichletInclusion_injective K) e hJn hT hM hq hC he
    (fun t => principalFormOperator K (A t)) hAc hAb
    (fun t => principalEnergy K (A t))
    (fun t => principalFormOperator_pairing K (A t)) (fun _ _ => rfl)
    L hLc hLb hsmall u₀

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial
