import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.UniformInitialTrace
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.DirichletWeak

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem localizedDirichletValue_test_pair (K : Set V)
    (χ f X : 𝓢(V, ℝ)) (u : dirichletForm K)
    (hX : X.toLp 2 volume = localizedDirichletValue K χ u)
    (hf : ∀ x, χ x * f x = f x) :
    inner ℝ (f.toLp 2 volume) (dirichletInclusion K u : L2) =
      inner ℝ (f.toLp 2 volume) (X.toLp 2 volume) := by
  have hm : schwartzMultiplier χ (f.toLp 2 volume) = f.toLp 2 volume := by
    rw [← schwartzProduct_toLp]
    congr 1
    ext x
    exact hf x
  rw [hX, localizedDirichletValue, ← schwartzMultiplier_selfAdjoint, hm]

theorem localized_vector_test_pair (K : Set V) (χ : 𝓢(V, ℝ))
    (u : PiLp 2 (fun _ : Fin m => dirichletForm K))
    (X f : Fin m → supportedTests K)
    (hX : ∀ j, (X j : 𝓢(V, ℝ)).toLp 2 volume = localizedDirichletValue K χ (u j))
    (hf : ∀ j x, χ x * (f j : 𝓢(V, ℝ)) x = (f j : 𝓢(V, ℝ)) x) :
    inner ℝ (vectorTestValue K f) (finiteHilbertMap (dirichletInclusion K) u) =
      inner ℝ (vectorTestValue K f) (vectorTestValue K X) := by
  simp only [PiLp.inner_apply, vectorTestValue, finiteHilbertMap_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact localizedDirichletValue_test_pair K χ (f j) (X j) (u j) (hX j) (hf j)

theorem weak_heat_local_test {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (hA : ∀ i j x, A i j x = A j i x)
    (B : Fin m → Fin m → Fin n → 𝓢(V, ℝ)) (C : Fin m → Fin m → 𝓢(V, ℝ))
    (χ : 𝓢(V, ℝ)) (W Z : PiLp 2 (fun _ : Fin m => dirichletForm K))
    (heq : ∀ z : PiLp 2 (fun _ : Fin m => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) Z) =
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
            (dirichletVectorLowerOrder hK B C W) - principalVectorEnergy K A z W)
    (X Y f : Fin m → supportedTests K)
    (hX : ∀ j, (X j : 𝓢(V, ℝ)).toLp 2 volume = localizedDirichletValue K χ (W j))
    (hY : ∀ j, (Y j : 𝓢(V, ℝ)).toLp 2 volume = localizedDirichletValue K χ (Z j))
    (hfχ : ∀ j x, χ x * (f j : 𝓢(V, ℝ)) x = (f j : 𝓢(V, ℝ)) x)
    (hadjχ : ∀ j x, χ x * (vectorTestAdjoint hK A B C f j : 𝓢(V, ℝ)) x =
      (vectorTestAdjoint hK A B C f j : 𝓢(V, ℝ)) x) :
    inner ℝ (vectorTestValue K f) (vectorTestValue K Y) =
      inner ℝ (vectorTestValue K f) (vectorTestValue K (vectorTestGenerator hK A B C X)) := by
  have he := heq (vectorTestForm K f)
  simp only [vectorTest_inclusion] at he
  have hadjW := vectorTestAdjoint_pair hK A hA B C f W
  have hadjX := vectorTestAdjoint_pair hK A hA B C f (vectorTestForm K X)
  have hgen := vectorTestGenerator_compatibility hK A B C X (vectorTestForm K f)
  simp only [vectorTest_inclusion] at hadjX hgen
  have hy := localized_vector_test_pair K χ Z Y f hY hfχ
  have hx := localized_vector_test_pair K χ W X (vectorTestAdjoint hK A B C f) hX hadjχ
  exact hy.symm.trans (he.trans (hadjW.trans (hx.trans (hadjX.symm.trans hgen.symm))))

theorem raw_weak_heat_local_test {K E : Set V} (hK : IsClosed K) (hE : IsClosed E)
    (hEK : E ⊆ K) {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (hηK : ∀ x ∈ K, η x = 1)
    (χ : 𝓢(V, ℝ)) (hχE : ∀ x ∈ E, χ x = 1)
    (W Z : PiLp 2 (fun _ : Fin n => dirichletForm K))
    (heq : ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) Z) =
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
            (rawLowerFormOperator D hK η hη W) -
              principalVectorEnergy K (rawCutoffPrincipalCoefficient g η hη) z W)
    (X Y : Fin n → supportedTests K)
    (hX : ∀ j, (X j : 𝓢(V, ℝ)).toLp 2 volume = localizedDirichletValue K χ (W j))
    (hY : ∀ j, (Y j : 𝓢(V, ℝ)).toLp 2 volume = localizedDirichletValue K χ (Z j))
    (f : Fin n → supportedTests E) :
    inner ℝ (vectorTestValue K (fun j => supportedTestInclusion hEK (f j)))
        (vectorTestValue K Y) =
      inner ℝ (vectorTestValue K (fun j => supportedTestInclusion hEK (f j)))
        (vectorTestValue K (vectorTestGenerator hK (rawCutoffPrincipalCoefficient g η hη)
          (rawCutoffFirstComponent D η hη) (rawCutoffZeroComponent D η hη) X)) := by
  let fK : Fin n → supportedTests K := fun j => supportedTestInclusion hEK (f j)
  apply weak_heat_local_test hK (rawCutoffPrincipalCoefficient g η hη)
    (rawCutoffPrincipalCoefficient_symmetric g η hη)
    (rawCutoffFirstComponent D η hη) (rawCutoffZeroComponent D η hη) χ W Z heq
    X Y fK hX hY
  · intro j x
    by_cases hx : x ∈ E
    · rw [hχE x hx, one_mul]
    · change χ x * (f j : 𝓢(V, ℝ)) x = (f j : 𝓢(V, ℝ)) x
      rw [(f j).property x hx, mul_zero]
  · intro j x
    by_cases hx : x ∈ E
    · rw [hχE x hx, one_mul]
    · have hz : (vectorTestAdjoint hK (rawCutoffPrincipalCoefficient g η hη)
          (rawCutoffFirstComponent D η hη) (rawCutoffZeroComponent D η hη) fK j :
            𝓢(V, ℝ)) x = 0 := by
        rw [raw_vectorTestAdjoint_apply hK D η hη hηK fK j x]
        exact rawTestAdjoint_zero_off hE D f j hx
      rw [hz, mul_zero]

end PoincareConjecture.M35.Uniqueness.Heat
