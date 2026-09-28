import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalResponse
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormHeatEquivalent










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped Topology SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)



theorem exists_principal_nonautonomous_tolerance {K : Set V} (hK : IsCompact K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) {ell : ℝ} (hEll : 0 < ell)
    (hA : ∀ i j x, A i j x = A j i x)
    (hell : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ T : ℝ, 0 ≤ T → T ≤ 1 →
      ∀ R : ℝ → dirichletForm K →L[ℝ] dirichletForm K,
      AEStronglyMeasurable R (timeMeasure T) →
      (∀ᵐ t ∂timeMeasure T, ‖R t‖ ≤ δ) →
      ∀ F : ℝ → dirichletForm K, MemLp F 2 (timeMeasure T) →
      ∃ (v : ℝ → dirichletForm K) (U : ℝ → dirichletValue K),
        MemLp v 2 (timeMeasure T) ∧ U 0 = 0 ∧ ContinuousOn U (Icc 0 T) ∧
        (∀ᵐ t ∂timeMeasure T, dirichletInclusion K (v t) = U t) ∧
        (∀ᵐ t ∂timeMeasure T, ∀ w : dirichletForm K,
          HasDerivWithinAt (fun s => inner ℝ (dirichletInclusion K w) (U s))
            (inner ℝ w (R t (v t) + F t) - principalEnergy K A w (v t)) (Icc 0 T) t) := by
  let C := weightedCore hK.isClosed A hEll hA hell
  have hC := weightedCore_continuous hK.isClosed A hEll hA hell
  have hCb := weightedCore_bounded hK.isClosed A hEll hA hell
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
  let L := e.toContinuousLinearMap
  let J : WeightedForm K →L[ℝ] dirichletValue K := (dirichletInclusion K).comp L
  have hJn : ‖J‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    have hE : 0 ≤ principalEnergy K A (e u) (e u) :=
      (mul_nonneg hEll.le (Finset.sum_nonneg (fun i _ => sq_nonneg _))).trans
        (principalEnergy_coercive hK.isClosed A hell (e u))
    have hs : ‖J u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq u]
      change ‖dirichletInclusion K (e u)‖ ^ 2 ≤ principalFormPairing K A (e u) (e u)
      simp only [principalFormPairing, real_inner_self_eq_norm_sq]
      linarith only [hE]
    simpa only [one_mul] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs
  exact exists_equivalent_nonautonomous_tolerance (dirichletInclusion K)
    (isCompactOperator_dirichletInclusion hK) (dirichletInclusion_denseRange K)
    (dirichletInclusion_injective K) e hJn (principalEnergy K A) (fun _ _ => rfl)

end PoincareConjecture.M35.Uniqueness.Heat
