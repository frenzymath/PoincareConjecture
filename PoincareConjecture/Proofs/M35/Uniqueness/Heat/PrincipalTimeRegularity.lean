import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FiniteTimeRegularity
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.PrincipalSegment
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalNormEstimates









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

theorem contDiffAt_principalValueHeat
    {K : Set V} (hK : IsCompact K) (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    {ell T B M q C : ℝ} (hell : 0 < ell) (hT : 0 < T) (hTB : 2 * T ≤ B)
    (hM : 0 ≤ M) (hq : 0 ≤ q) (hC : 0 ≤ C) (hscale : 1 ≤ min 1 ell * M ^ 2)
    (hA : ∀ i j x, A 0 i j x = A 0 j i x)
    (hEll : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A 0 i j x * ξ i * ξ j)
    (hAc : ContDiffOn ℝ ∞ (fun t => principalFormOperator K (A t)) (Icc 0 B))
    (hAb : ∀ t ∈ Icc 0 T,
      ‖principalFormOperator K (A 0) - principalFormOperator K (A t)‖ ≤ q)
    (L : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletValue K))
    (hLc : ContDiffOn ℝ ∞ L (Icc 0 B)) (hLb : ∀ t ∈ Icc 0 T, ‖L t‖ ≤ C)
    (hsmall : (T + 1) * (M * (q * M)) +
      (Real.sqrt T * (Real.sqrt T + 1)) * (C * M) < 1)
    {u₀ : PiLp 2 (fun _ : Fin m => dirichletValue K)}
    {v : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K)}
    {U : ℝ → PiLp 2 (fun _ : Fin m => dirichletValue K)}
    (hsol : PrincipalValueHeat K A L 0 B u₀ v U)
    {t : ℝ} (ht : t ∈ Ioc 0 T) : ContDiffAt ℝ ∞ U t := by
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
  have hnorm (u : WeightedForm K) : principalFormPairing K (A 0) (e u) (e u) = ‖u‖ ^ 2 :=
    real_inner_self_eq_norm_sq u
  have hJn : ‖J‖ ≤ 1 :=
    norm_principal_equivalent_inclusion_le_one hK.isClosed (A 0) hell hEll e hnorm
  have he : ‖e.toContinuousLinearMap‖ ≤ M :=
    norm_principal_equivalence_le hK.isClosed (A 0) hM hscale hEll e hnorm
  have hbase (w u : WeightedForm K) : inner ℝ w u =
      inner ℝ (dirichletInclusion K (e w)) (dirichletInclusion K (e u)) +
        inner ℝ (e w) (principalFormOperator K (A 0) (e u)) := by
    exact (show inner ℝ w u =
      inner ℝ (dirichletInclusion K (e w)) (dirichletInclusion K (e u)) +
        principalEnergy K (A 0) (e w) (e u) from rfl).trans
      (congrArg (fun q => inner ℝ (dirichletInclusion K (e w))
        (dirichletInclusion K (e u)) + q)
        (principalFormOperator_pairing K (A 0) (e w) (e u)).symm)
  have heq : ∀ s ∈ Icc 0 B, ∀ w : PiLp 2 (fun _ : Fin m => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (U s) =
        inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (U 0) +
          ∫ r in (0 : ℝ)..s, inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (L r (v r)) -
            ∑ i, inner ℝ (w i) (principalFormOperator K (A r) (v r i)) := by
    simpa only [principalFormOperator_pairing, principalVectorEnergy, hsol.2.1, zero_add]
      using hsol.2.2.2.2.2
  exact contDiffAt_finite_equivalent_weak_value (dirichletInclusion K)
    (isCompactOperator_dirichletInclusion hK) (dirichletInclusion_denseRange K)
    (dirichletInclusion_injective K) e hJn hT hTB hM hq hC he
    (fun s => principalFormOperator K (A s)) hAc hAb L hLc hLb
    hbase hsmall hsol.1 hsol.2.2.1 hsol.2.2.2.1 heq ht

end PoincareConjecture.M35.Uniqueness.Heat
