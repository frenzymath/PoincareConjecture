import PoincareConjecture.Proofs.M35.Uniqueness.Heat.VectorMixedHeat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem exists_principal_vector_mixed_initial_heat
    {K : Set V} (hK : IsCompact K) (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    {ell b : ℝ} (hell : 0 < ell) (hb : 0 < b)
    (hA : ∀ i j x, A 0 i j x = A 0 j i x)
    (hEll : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A 0 i j x * ξ i * ξ j)
    (hAc : ContinuousOn (fun t => principalFormOperator K (A t)) (Icc 0 b))
    (L : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletValue K))
    (hLc : ContinuousOn L (Icc 0 b)) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ T < b ∧
      ∀ v₀ : PiLp 2 (fun _ : Fin m => dirichletForm K),
      ∃ (v : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K))
        (U : ℝ → PiLp 2 (fun _ : Fin m => dirichletValue K)),
        MemLp v 2 (timeMeasure T) ∧ U 0 = finiteHilbertMap (dirichletInclusion K) v₀ ∧
        ContinuousOn U (Icc 0 T) ∧
        (∀ᵐ t ∂timeMeasure T, finiteHilbertMap (dirichletInclusion K) (v t) = U t) ∧
        (∀ᵐ t ∂timeMeasure T, ∀ w : PiLp 2 (fun _ : Fin m => dirichletForm K),
          HasDerivWithinAt (fun s => inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (U s))
            (inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (L t (v t)) -
              principalVectorEnergy K (A t) w (v t)) (Icc 0 T) t) := by
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
  exact exists_finite_equivalent_mixed_initial_heat (dirichletInclusion K)
    (isCompactOperator_dirichletInclusion hK) (dirichletInclusion_denseRange K)
    (dirichletInclusion_injective K) e hJn hb
    (fun t => principalFormOperator K (A t)) hAc
    (fun t => principalEnergy K (A t))
    (fun t => principalFormOperator_pairing K (A t)) (fun _ _ => rfl) L hLc

end PoincareConjecture.M35.Uniqueness.Heat
