import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TestGenerator
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.DirichletWeak









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

def lowerTestAdjoint {K : Set V} (hK : IsClosed K)
    (B : Fin n → 𝓢(V, ℝ)) (C : 𝓢(V, ℝ)) (f : supportedTests K) : supportedTests K :=
  -(∑ i, testPartial hK i (testMultiplier K (B i) f)) + testMultiplier K C f

theorem dirichlet_multiplier_test_pair (K : Set V) (a : 𝓢(V, ℝ))
    (f : supportedTests K) (u : dirichletValue K) :
    inner ℝ (intoDirichletValue K f) (dirichletValueMultiplier K a u) =
      inner ℝ (intoDirichletValue K (testMultiplier K a f)) u := by
  change inner ℝ ((f : 𝓢(V, ℝ)).toLp 2 volume) (schwartzMultiplier a (u : L2)) =
    inner ℝ ((testMultiplier K a f : 𝓢(V, ℝ)).toLp 2 volume) (u : L2)
  rw [testMultiplier_toLp, schwartzMultiplier_selfAdjoint]

theorem dirichlet_partial_test_pair {K : Set V} (hK : IsClosed K)
    (i : Fin n) (f : supportedTests K) (u : dirichletForm K) :
    inner ℝ (intoDirichletValue K f) (dirichletPartialValue hK i u) =
      -inner ℝ (intoDirichletValue K (testPartial hK i f)) (dirichletInclusion K u) := by
  have h := dirichletPartial_weak K u i (f : 𝓢(V, ℝ))
  change inner ℝ ((f : 𝓢(V, ℝ)).toLp 2 volume) (dirichletPartial K i u) =
    -inner ℝ ((∂_{EuclideanSpace.single i (1 : ℝ)} (f : 𝓢(V, ℝ))).toLp 2 volume)
      (dirichletInclusion K u : L2)
  rw [real_inner_comm, h, real_inner_comm (dirichletInclusion K u : L2)]

theorem lowerTestAdjoint_pair {K : Set V} (hK : IsClosed K)
    (B : Fin n → 𝓢(V, ℝ)) (C : 𝓢(V, ℝ))
    (f : supportedTests K) (u : dirichletForm K) :
    inner ℝ (intoDirichletValue K f) (dirichletLowerOrder hK B C u) =
      inner ℝ (intoDirichletValue K (lowerTestAdjoint hK B C f)) (dirichletInclusion K u) := by
  simp only [dirichletLowerOrder, sum_apply, add_apply, ContinuousLinearMap.comp_apply,
    inner_add_right, inner_sum, lowerTestAdjoint, map_add, map_neg, map_sum,
    inner_add_left, inner_neg_left, sum_inner]
  simp only [dirichlet_multiplier_test_pair, dirichlet_partial_test_pair, Finset.sum_neg_distrib]

def vectorTestAdjoint {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (B : Fin m → Fin m → Fin n → 𝓢(V, ℝ))
    (C : Fin m → Fin m → 𝓢(V, ℝ)) (f : Fin m → supportedTests K) :
    Fin m → supportedTests K := fun j =>
  principalTestLaplacian hK A (f j) + ∑ i, lowerTestAdjoint hK (B i j) (C i j) (f i)

theorem vector_lower_adjoint_pair {K : Set V} (hK : IsClosed K)
    (B : Fin m → Fin m → Fin n → 𝓢(V, ℝ)) (C : Fin m → Fin m → 𝓢(V, ℝ))
    (f : Fin m → supportedTests K) (u : PiLp 2 (fun _ : Fin m => dirichletForm K)) :
    inner ℝ (vectorTestValue K f) (dirichletVectorLowerOrder hK B C u) =
      inner ℝ (vectorTestValue K
        (fun j => ∑ i, lowerTestAdjoint hK (B i j) (C i j) (f i)))
          (finiteHilbertMap (dirichletInclusion K) u) := by
  simp only [dirichletVectorLowerOrder, PiLp.inner_apply, finiteHilbertMatrix_apply,
    finiteHilbertMap_apply, vectorTestValue,
    inner_sum, lowerTestAdjoint_pair, map_sum, sum_inner]
  exact Finset.sum_comm

theorem principalVectorEnergy_test_symm {K : Set V}
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (hA : ∀ i j x, A i j x = A j i x)
    (f : Fin m → supportedTests K) (u : PiLp 2 (fun _ : Fin m => dirichletForm K)) :
    principalVectorEnergy K A (vectorTestForm K f) u =
      principalVectorEnergy K A u (vectorTestForm K f) := by
  apply Finset.sum_congr rfl
  intro i _
  exact principalEnergy_symmetric K A hA _ _

theorem vectorTestAdjoint_pair {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (hA : ∀ i j x, A i j x = A j i x)
    (B : Fin m → Fin m → Fin n → 𝓢(V, ℝ)) (C : Fin m → Fin m → 𝓢(V, ℝ))
    (f : Fin m → supportedTests K) (u : PiLp 2 (fun _ : Fin m => dirichletForm K)) :
    inner ℝ (vectorTestValue K f) (dirichletVectorLowerOrder hK B C u) -
        principalVectorEnergy K A (vectorTestForm K f) u =
      inner ℝ (vectorTestValue K (vectorTestAdjoint hK A B C f))
        (finiteHilbertMap (dirichletInclusion K) u) := by
  have he : vectorTestValue K (vectorTestAdjoint hK A B C f) =
      vectorTestValue K (fun j => principalTestLaplacian hK A (f j)) +
        vectorTestValue K (fun j => ∑ i, lowerTestAdjoint hK (B i j) (C i j) (f i)) := by
    apply PiLp.ext
    intro j
    exact map_add (intoDirichletValue K) _ _
  have hv := congrArg (fun w : PiLp 2 (fun _ : Fin m => dirichletValue K) =>
    inner ℝ w (finiteHilbertMap (dirichletInclusion K) u)) he
  rw [inner_add_left] at hv
  have hl := vector_lower_adjoint_pair hK B C f u
  have hp := (principalVectorEnergy_test_symm A hA f u).trans
    (principalVectorEnergy_into_laplacian hK A f u)
  rw [real_inner_comm] at hp
  linarith only [hv, hl, hp]

end PoincareConjecture.M35.Uniqueness.Heat
