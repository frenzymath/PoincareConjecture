import PoincareConjecture.Proofs.M35.Uniqueness.Heat.SecondVectorHeat
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalNormEstimates









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem exists_principal_second_vector_heat
    {K : Set V} (hK : IsCompact K) (A A₁ A₂ : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    {ell b : ℝ} (hell : 0 < ell) (hb : 0 < b)
    (hA : ∀ i j x, A 0 i j x = A 0 j i x)
    (hEll : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A 0 i j x * ξ i * ξ j)
    (hAc : ContDiffOn ℝ 1 (fun t => principalFormOperator K (A t)) (Icc 0 b))
    (hA₁c : ContDiffOn ℝ 1 (fun t => principalFormOperator K (A₁ t)) (Icc 0 b))
    (hA₂c : ContinuousOn (fun t => principalFormOperator K (A₂ t)) (Icc 0 b))
    (hAd : ∀ t ∈ Ioo 0 b, HasDerivAt (fun s => principalFormOperator K (A s))
      (principalFormOperator K (A₁ t)) t)
    (hA₁d : ∀ t ∈ Ioo 0 b, HasDerivAt (fun s => principalFormOperator K (A₁ s))
      (principalFormOperator K (A₂ t)) t)
    (L L₁ L₂ : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletValue K))
    (hLc : ContDiffOn ℝ 1 L (Icc 0 b)) (hL₁c : ContDiffOn ℝ 1 L₁ (Icc 0 b))
    (hL₂c : ContinuousOn L₂ (Icc 0 b))
    (hLd : ∀ t ∈ Ioo 0 b, HasDerivAt L (L₁ t) t)
    (hL₁d : ∀ t ∈ Ioo 0 b, HasDerivAt L₁ (L₂ t) t) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ T < b ∧
      ∀ u₀ w₀ z₀ : PiLp 2 (fun _ : Fin m => dirichletForm K),
      (∀ z : PiLp 2 (fun _ : Fin m => dirichletForm K),
        inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
          (finiteHilbertMap (dirichletInclusion K) w₀) =
            inner ℝ (finiteHilbertMap (dirichletInclusion K) z) (L 0 u₀) -
              principalVectorEnergy K (A 0) z u₀) →
      (∀ z : PiLp 2 (fun _ : Fin m => dirichletForm K),
        inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
          (finiteHilbertMap (dirichletInclusion K) z₀) =
            inner ℝ (finiteHilbertMap (dirichletInclusion K) z) (L 0 w₀) -
              principalVectorEnergy K (A 0) z w₀ +
            inner ℝ (finiteHilbertMap (dirichletInclusion K) z) (L₁ 0 u₀) -
              principalVectorEnergy K (A₁ 0) z u₀) →
      ∃ u w : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K), u 0 = u₀ ∧ w 0 = w₀ ∧
        ContinuousOn u (Icc 0 T) ∧ ContinuousOn w (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt u (w t) (Icc 0 T) t) ∧
        ∀ t ∈ Icc 0 T, ∀ z : PiLp 2 (fun _ : Fin m => dirichletForm K),
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
            (finiteHilbertMap (dirichletInclusion K) (w t)) =
              inner ℝ (finiteHilbertMap (dirichletInclusion K) z) (L t (u t)) -
                principalVectorEnergy K (A t) z (u t) := by
  let C := weightedCore hK.isClosed (A 0) hell hA hEll
  have hC := weightedCore_continuous hK.isClosed (A 0) hell hA hEll
  have hCb := weightedCore_bounded hK.isClosed (A 0) hell hA hEll
  let : NormedAddCommGroup (WeightedForm K) := C.toNormedAddCommGroupOfTopology hC hCb
  let : InnerProductSpace ℝ (WeightedForm K) := InnerProductSpace.ofCoreOfTopology C hC hCb
  let e : WeightedForm K ≃L[ℝ] dirichletForm K :=
    { LinearEquiv.refl ℝ (dirichletForm K) with
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }
  let eu : WeightedForm K ≃ᵤ dirichletForm K :=
    { e.toEquiv with
      uniformContinuous_toFun := e.toContinuousLinearMap.uniformContinuous
      uniformContinuous_invFun := e.symm.toContinuousLinearMap.uniformContinuous }
  let : CompleteSpace (WeightedForm K) := eu.completeSpace_iff.mpr inferInstance
  have hnorm (u : WeightedForm K) : principalFormPairing K (A 0) (e u) (e u) = ‖u‖ ^ 2 :=
    real_inner_self_eq_norm_sq u
  have hJn := norm_principal_equivalent_inclusion_le_one hK.isClosed (A 0) hell hEll e hnorm
  exact exists_finite_equivalent_second_heat (dirichletInclusion K)
    (isCompactOperator_dirichletInclusion hK) (dirichletInclusion_denseRange K)
    (dirichletInclusion_injective K) e hJn hb
    (fun t => principalFormOperator K (A t)) (fun t => principalFormOperator K (A₁ t))
    (fun t => principalFormOperator K (A₂ t)) hAc hA₁c hA₂c hAd hA₁d
    (fun t => principalEnergy K (A t)) (fun t => principalEnergy K (A₁ t))
    (fun t => principalFormOperator_pairing K (A t))
    (fun t => principalFormOperator_pairing K (A₁ t)) (fun _ _ => rfl)
    L L₁ L₂ hLc hL₁c hL₂c hLd hL₁d

end PoincareConjecture.M35.Uniqueness.Heat
