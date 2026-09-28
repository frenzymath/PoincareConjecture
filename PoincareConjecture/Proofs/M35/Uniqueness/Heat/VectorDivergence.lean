import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TestGenerator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

section Finite

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] {m : ℕ}

theorem finiteHilbertMap_single (J : V →L[ℝ] H) (i : Fin m) (v : V) :
    finiteHilbertMap J (finiteHilbertSingle i v) = finiteHilbertSingle i (J v) := by
  apply PiLp.ext
  intro j
  by_cases hji : j = i <;> simp only [finiteHilbertMap_apply,
    finiteHilbertSingle_apply, hji, if_true, if_false, map_zero]

theorem inner_finiteHilbertSingle_left (i : Fin m) (v : H)
    (u : PiLp 2 (fun _ : Fin m => H)) :
    inner ℝ (finiteHilbertSingle i v) u = inner ℝ v (u i) := by
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · simp only [finiteHilbertSingle_apply, if_true]
  · intro j _ hji
    simp only [finiteHilbertSingle_apply, hji, if_false, inner_zero_left]
  · simp

theorem inner_finiteHilbertMap_single (J : V →L[ℝ] H) (i : Fin m) (v : V)
    (u : PiLp 2 (fun _ : Fin m => H)) :
    inner ℝ (finiteHilbertMap J (finiteHilbertSingle i v)) u = inner ℝ (J v) (u i) := by
  rw [finiteHilbertMap_single, inner_finiteHilbertSingle_left]

end Finite

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem principalVectorEnergy_single_left (K : Set V)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (k : Fin m) (v : dirichletForm K)
    (u : PiLp 2 (fun _ : Fin m => dirichletForm K)) :
    principalVectorEnergy K A (finiteHilbertSingle k v) u = principalEnergy K A v (u k) := by
  unfold principalVectorEnergy
  rw [Finset.sum_eq_single k]
  · simp only [finiteHilbertSingle_apply, if_true]
  · intro i _ hik
    simp only [finiteHilbertSingle_apply, hik, if_false, principalEnergy, map_zero,
      inner_zero_left, Finset.sum_const_zero]
  · simp

theorem vector_component_divergence (K : Set V)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (hA : ∀ i j x, A i j x = A j i x)
    (u : PiLp 2 (fun _ : Fin m => dirichletForm K))
    (B Z : PiLp 2 (fun _ : Fin m => dirichletValue K))
    (heq : ∀ z : PiLp 2 (fun _ : Fin m => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z) Z =
        inner ℝ (finiteHilbertMap (dirichletInclusion K) z) B - principalVectorEnergy K A z u)
    (k : Fin m) (φ : supportedTests K) :
    principalEnergy K A (u k) (intoDirichletForm K φ) =
      inner ℝ ((B k : L2) - (Z k : L2)) ((φ : 𝓢(V, ℝ)).toLp 2 volume) := by
  have h := heq (finiteHilbertSingle k (intoDirichletForm K φ))
  have hZ := inner_finiteHilbertMap_single (dirichletInclusion K) k
    (intoDirichletForm K φ) Z
  have hB := inner_finiteHilbertMap_single (dirichletInclusion K) k
    (intoDirichletForm K φ) B
  have hE := (principalVectorEnergy_single_left K A k (intoDirichletForm K φ) u).trans
    (principalEnergy_symmetric K A hA (intoDirichletForm K φ) (u k))
  have hout : principalEnergy K A (u k) (intoDirichletForm K φ) =
      inner ℝ (dirichletInclusion K (intoDirichletForm K φ)) (B k) -
        inner ℝ (dirichletInclusion K (intoDirichletForm K φ)) (Z k) := by
    linarith only [h, hZ, hB, hE]
  change principalEnergy K A (u k) (intoDirichletForm K φ) =
    inner ℝ ((φ : 𝓢(V, ℝ)).toLp 2 volume) (B k : L2) -
      inner ℝ ((φ : 𝓢(V, ℝ)).toLp 2 volume) (Z k : L2) at hout
  rw [inner_sub_left]
  exact hout.trans (congrArg₂ (· - ·) (real_inner_comm _ _) (real_inner_comm _ _))

end PoincareConjecture.M35.Uniqueness.Heat
