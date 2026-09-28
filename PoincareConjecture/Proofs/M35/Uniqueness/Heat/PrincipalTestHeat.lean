import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalStrongHeat
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TestGenerator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem exists_principal_test_heat
    {K : Set V} (hK : IsCompact K) (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    (B : ℝ → Fin m → Fin m → Fin n → 𝓢(V, ℝ))
    (C : ℝ → Fin m → Fin m → 𝓢(V, ℝ))
    {ell b : ℝ} (hell : 0 < ell) (hb : 0 < b)
    (hA : ∀ i j x, A 0 i j x = A 0 j i x)
    (hEll : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A 0 i j x * ξ i * ξ j)
    (hAc : ContDiffOn ℝ 1 (fun t => principalFormOperator K (A t)) (Icc 0 b))
    (hLc : ContDiffOn ℝ 1 (fun t => dirichletVectorLowerOrder hK.isClosed (B t) (C t))
      (Icc 0 b)) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ T < b ∧ ∀ f : Fin m → supportedTests K,
      ∃ (u : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K))
        (Z : ℝ → PiLp 2 (fun _ : Fin m => dirichletValue K)),
        u 0 = vectorTestForm K f ∧
        ContinuousOn u (Icc 0 T) ∧ ContinuousOn Z (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt
          (fun s => finiteHilbertMap (dirichletInclusion K) (u s)) (Z t) (Icc 0 T) t) ∧
        (∀ t ∈ Icc 0 T, ∀ z : PiLp 2 (fun _ : Fin m => dirichletForm K),
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z) (Z t) =
            inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
              (dirichletVectorLowerOrder hK.isClosed (B t) (C t) (u t)) -
                principalVectorEnergy K (A t) z (u t)) ∧
        ∃ w : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K),
          MemLp w 2 (SpectralHeatNative.timeMeasure T) ∧
          ∀ᵐ t ∂SpectralHeatNative.timeMeasure T,
            HasDerivAt u (w t) t ∧ finiteHilbertMap (dirichletInclusion K) (w t) = Z t := by
  refine (exists_principal_strong_vector_heat hK A hell hb
    hA hEll hAc (fun t => dirichletVectorLowerOrder hK.isClosed (B t) (C t)) hLc).elim ?_
  intro T hT
  refine ⟨T, hT.1, hT.2.1, hT.2.2.1, ?_⟩
  intro f
  refine (hT.2.2.2 (vectorTestForm K f)
    (vectorTestForm K (vectorTestGenerator hK.isClosed (A 0) (B 0) (C 0) f))
      (vectorTestGenerator_compatibility hK.isClosed (A 0) (B 0) (C 0) f)).elim ?_
  intro u hu
  refine hu.elim ?_
  intro Z hZ
  exact ⟨u, Z, hZ.1, hZ.2.2.1, hZ.2.2.2.1, hZ.2.2.2.2.1, hZ.2.2.2.2.2⟩

end PoincareConjecture.M35.Uniqueness.Heat
