import PoincareConjecture.Proofs.M35.Uniqueness.Heat.DirichletVectorLowerOrder
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FiniteHilbertOperator










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

def lowerTestOperator {K : Set V} (hK : IsClosed K)
    (B : Fin n → 𝓢(V, ℝ)) (C : 𝓢(V, ℝ)) : supportedTests K →ₗ[ℝ] supportedTests K :=
  (∑ i, (testMultiplier K (B i)).comp (testPartial hK i)) + testMultiplier K C

theorem dirichletLowerOrder_into {K : Set V} (hK : IsClosed K)
    (B : Fin n → 𝓢(V, ℝ)) (C : 𝓢(V, ℝ)) (f : supportedTests K) :
    dirichletLowerOrder hK B C (intoDirichletForm K f) =
      intoDirichletValue K (lowerTestOperator hK B C f) := by
  simp only [dirichletLowerOrder, lowerTestOperator, add_apply,
    sum_apply, LinearMap.add_apply, LinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, LinearMap.comp_apply,
    dirichletPartialValue_into, dirichletInclusion_into,
    dirichletValueMultiplier_into, map_add, map_sum]

theorem principalEnergy_into_laplacian {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (f : supportedTests K) (u : dirichletForm K) :
    principalEnergy K A u (intoDirichletForm K f) =
      -inner ℝ (dirichletInclusion K u)
        (intoDirichletValue K (principalTestLaplacian hK A f)) := by
  have h := principalForm_pairing_laplacian hK A f u
  simp only [principalFormPairing, dirichletInclusion_into, inner_sub_right] at h
  linarith only [h]

def vectorTestForm (K : Set V) (f : Fin m → supportedTests K) :
    PiLp 2 (fun _ : Fin m => dirichletForm K) :=
  WithLp.toLp 2 (fun i => intoDirichletForm K (f i))

def vectorTestValue (K : Set V) (f : Fin m → supportedTests K) :
    PiLp 2 (fun _ : Fin m => dirichletValue K) :=
  WithLp.toLp 2 (fun i => intoDirichletValue K (f i))

theorem vectorTest_inclusion (K : Set V) (f : Fin m → supportedTests K) :
    finiteHilbertMap (dirichletInclusion K) (vectorTestForm K f) = vectorTestValue K f := by
  apply PiLp.ext
  intro i
  rfl

def vectorTestGenerator {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (B : Fin m → Fin m → Fin n → 𝓢(V, ℝ))
    (C : Fin m → Fin m → 𝓢(V, ℝ)) (f : Fin m → supportedTests K) :
    Fin m → supportedTests K := fun i =>
  principalTestLaplacian hK A (f i) + ∑ j, lowerTestOperator hK (B i j) (C i j) (f j)

theorem dirichletVectorLowerOrder_into {K : Set V} (hK : IsClosed K)
    (B : Fin m → Fin m → Fin n → 𝓢(V, ℝ)) (C : Fin m → Fin m → 𝓢(V, ℝ))
    (f : Fin m → supportedTests K) :
    dirichletVectorLowerOrder hK B C (vectorTestForm K f) =
      vectorTestValue K (fun i => ∑ j, lowerTestOperator hK (B i j) (C i j) (f j)) := by
  apply PiLp.ext
  intro i
  rw [dirichletVectorLowerOrder, finiteHilbertMatrix_apply]
  change (∑ j, dirichletLowerOrder hK (B i j) (C i j) (intoDirichletForm K (f j))) =
    intoDirichletValue K (∑ j, lowerTestOperator hK (B i j) (C i j) (f j))
  simp only [dirichletLowerOrder_into, map_sum]

theorem principalVectorEnergy_into_laplacian {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (f : Fin m → supportedTests K)
    (u : PiLp 2 (fun _ : Fin m => dirichletForm K)) :
    principalVectorEnergy K A u (vectorTestForm K f) =
      -inner ℝ (finiteHilbertMap (dirichletInclusion K) u)
        (vectorTestValue K (fun i => principalTestLaplacian hK A (f i))) := by
  change (∑ i, principalEnergy K A (u i) (intoDirichletForm K (f i))) = _
  simp only [principalEnergy_into_laplacian hK, PiLp.inner_apply,
    finiteHilbertMap_apply, Finset.sum_neg_distrib, vectorTestValue]

theorem vectorTestGenerator_value {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (B : Fin m → Fin m → Fin n → 𝓢(V, ℝ))
    (C : Fin m → Fin m → 𝓢(V, ℝ)) (f : Fin m → supportedTests K) :
    vectorTestValue K (vectorTestGenerator hK A B C f) =
      vectorTestValue K (fun i => principalTestLaplacian hK A (f i)) +
        dirichletVectorLowerOrder hK B C (vectorTestForm K f) := by
  rw [dirichletVectorLowerOrder_into]
  apply PiLp.ext
  intro i
  exact map_add (intoDirichletValue K) _ _

theorem vectorTestGenerator_compatibility {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (B : Fin m → Fin m → Fin n → 𝓢(V, ℝ))
    (C : Fin m → Fin m → 𝓢(V, ℝ)) (f : Fin m → supportedTests K)
    (z : PiLp 2 (fun _ : Fin m => dirichletForm K)) :
    inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
      (finiteHilbertMap (dirichletInclusion K)
        (vectorTestForm K (vectorTestGenerator hK A B C f))) =
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (dirichletVectorLowerOrder hK B C (vectorTestForm K f)) -
          principalVectorEnergy K A z (vectorTestForm K f) := by
  have hvalue := congrArg (fun v => inner ℝ (finiteHilbertMap (dirichletInclusion K) z) v)
    (vectorTestGenerator_value hK A B C f)
  have henergy := principalVectorEnergy_into_laplacian hK A f z
  rw [inner_add_right] at hvalue
  have hinc := congrArg (fun v : PiLp 2 (fun _ : Fin m => dirichletValue K) =>
    inner ℝ (finiteHilbertMap (dirichletInclusion K) z) v)
      (vectorTest_inclusion K (vectorTestGenerator hK A B C f))
  exact hinc.trans (by linarith only [hvalue, henergy])

end PoincareConjecture.M35.Uniqueness.Heat
