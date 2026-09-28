import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalSecondHeat
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

theorem exists_principal_second_test_heat
    {K : Set V} (hK : IsCompact K) (A A₁ A₂ : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    (B B₁ B₂ : ℝ → Fin m → Fin m → Fin n → 𝓢(V, ℝ))
    (C C₁ C₂ : ℝ → Fin m → Fin m → 𝓢(V, ℝ))
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
    (hLc : ContDiffOn ℝ 1 (fun t => dirichletVectorLowerOrder hK.isClosed (B t) (C t))
      (Icc 0 b))
    (hL₁c : ContDiffOn ℝ 1 (fun t => dirichletVectorLowerOrder hK.isClosed (B₁ t) (C₁ t))
      (Icc 0 b))
    (hL₂c : ContinuousOn (fun t => dirichletVectorLowerOrder hK.isClosed (B₂ t) (C₂ t))
      (Icc 0 b))
    (hLd : ∀ t ∈ Ioo 0 b, HasDerivAt
      (fun s => dirichletVectorLowerOrder hK.isClosed (B s) (C s))
      (dirichletVectorLowerOrder hK.isClosed (B₁ t) (C₁ t)) t)
    (hL₁d : ∀ t ∈ Ioo 0 b, HasDerivAt
      (fun s => dirichletVectorLowerOrder hK.isClosed (B₁ s) (C₁ s))
      (dirichletVectorLowerOrder hK.isClosed (B₂ t) (C₂ t)) t) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ T < b ∧ ∀ f : Fin m → supportedTests K,
      ∃ u w : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K),
        u 0 = vectorTestForm K f ∧
        w 0 = vectorTestForm K (vectorTestGenerator hK.isClosed (A 0) (B 0) (C 0) f) ∧
        ContinuousOn u (Icc 0 T) ∧ ContinuousOn w (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, HasDerivWithinAt u (w t) (Icc 0 T) t) ∧
        ∀ t ∈ Icc 0 T, ∀ z : PiLp 2 (fun _ : Fin m => dirichletForm K),
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
            (finiteHilbertMap (dirichletInclusion K) (w t)) =
              inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
                (dirichletVectorLowerOrder hK.isClosed (B t) (C t) (u t)) -
                  principalVectorEnergy K (A t) z (u t) := by
  refine (exists_principal_second_vector_heat (m := m) hK A A₁ A₂
    hell hb hA hEll hAc hA₁c hA₂c hAd hA₁d
    (fun t => dirichletVectorLowerOrder hK.isClosed (B t) (C t))
    (fun t => dirichletVectorLowerOrder hK.isClosed (B₁ t) (C₁ t))
    (fun t => dirichletVectorLowerOrder hK.isClosed (B₂ t) (C₂ t))
    hLc hL₁c hL₂c hLd hL₁d).elim ?_
  intro T hT
  refine ⟨T, hT.1, hT.2.1, hT.2.2.1, ?_⟩
  intro f
  let g := vectorTestGenerator hK.isClosed (A 0) (B 0) (C 0) f
  let z₀ := vectorTestForm K (vectorTestGenerator hK.isClosed (A 0) (B 0) (C 0) g) +
    vectorTestForm K (vectorTestGenerator hK.isClosed (A₁ 0) (B₁ 0) (C₁ 0) f)
  apply hT.2.2.2 (vectorTestForm K f) (vectorTestForm K g) z₀
  · exact vectorTestGenerator_compatibility hK.isClosed (A 0) (B 0) (C 0) f
  · intro z
    simp only [z₀, map_add, inner_add_right,
      vectorTestGenerator_compatibility hK.isClosed]
    ring

end PoincareConjecture.M35.Uniqueness.Heat
