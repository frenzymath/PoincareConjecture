import PoincareConjecture.Proofs.M35.Uniqueness.Heat.InteriorFirstProducts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem dirichletLowerOrder_coe {K : Set V} (hK : IsClosed K)
    (B : Fin n → 𝓢(V, ℝ)) (C : 𝓢(V, ℝ)) (u : dirichletForm K) :
    (dirichletLowerOrder hK B C u : L2) =
      (∑ i, schwartzMultiplier (B i) (dirichletPartial K i u)) +
        schwartzMultiplier C (dirichletInclusion K u : L2) := by
  simp only [dirichletLowerOrder, add_apply, sum_apply, ContinuousLinearMap.comp_apply,
    Submodule.coe_add, Submodule.coe_sum]
  rfl

theorem exists_weak_derivative_localized_lowerOrder {K : Set V} (hK : IsClosed K)
    (B : Fin n → 𝓢(V, ℝ)) (C : 𝓢(V, ℝ)) (u : dirichletForm K)
    (hu : HasInteriorSecondDerivatives K u) (χ : 𝓢(V, ℝ))
    (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K) (j : Fin n) :
    ∃ d : L2, HasWeakSchwartzDerivative
      (schwartzMultiplier χ (dirichletLowerOrder hK B C u : L2)) d
        (EuclideanSpace.single j (1 : ℝ)) := by
  have hfirst (i : Fin n) : ∃ d : L2, HasWeakSchwartzDerivative
      (schwartzMultiplier (schwartzProduct χ (B i)) (dirichletPartial K i u)) d
        (EuclideanSpace.single j (1 : ℝ)) :=
    exists_weak_derivative_partial_product K u hu (schwartzProduct χ (B i))
      hχ.mul_right (tsupport_mul_subset_left.trans hχK) i j
  choose d hd using hfirst
  have hzero := (dirichletPartial_weak K u j).mul _ _ _ (schwartzProduct χ C)
  have hsum := (HasWeakSchwartzDerivative.sum _ d _ hd).add hzero
  have he : schwartzMultiplier χ (dirichletLowerOrder hK B C u : L2) =
      (∑ i, schwartzMultiplier (schwartzProduct χ (B i)) (dirichletPartial K i u)) +
        schwartzMultiplier (schwartzProduct χ C) (dirichletInclusion K u : L2) := by
    rw [dirichletLowerOrder_coe hK B C u, map_add, map_sum]
    simp only [schwartzMultiplier_product]
  exact ⟨_, weakSchwartzDerivative_congr he hsum⟩

theorem dirichletVectorLowerOrder_coe {K : Set V} (hK : IsClosed K)
    (B : Fin m → Fin m → Fin n → 𝓢(V, ℝ)) (C : Fin m → Fin m → 𝓢(V, ℝ))
    (u : PiLp 2 (fun _ : Fin m => dirichletForm K)) (k : Fin m) :
    (dirichletVectorLowerOrder hK B C u k : L2) =
      ∑ j, (dirichletLowerOrder hK (B k j) (C k j) (u j) : L2) := by
  rw [dirichletVectorLowerOrder, finiteHilbertMatrix_apply, Submodule.coe_sum]

theorem exists_weak_derivative_localized_vector_lowerOrder {K : Set V} (hK : IsClosed K)
    (B : Fin m → Fin m → Fin n → 𝓢(V, ℝ)) (C : Fin m → Fin m → 𝓢(V, ℝ))
    (u : PiLp 2 (fun _ : Fin m => dirichletForm K))
    (hu : ∀ k, HasInteriorSecondDerivatives K (u k)) (χ : 𝓢(V, ℝ))
    (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K) (k : Fin m) (j : Fin n) :
    ∃ d : L2, HasWeakSchwartzDerivative
      (schwartzMultiplier χ (dirichletVectorLowerOrder hK B C u k : L2)) d
        (EuclideanSpace.single j (1 : ℝ)) := by
  choose d hd using fun i => exists_weak_derivative_localized_lowerOrder hK
    (B k i) (C k i) (u i) (hu i) χ hχ hχK j
  have hsum := HasWeakSchwartzDerivative.finset_sum Finset.univ _ d _ (fun i _ => hd i)
  have he : schwartzMultiplier χ (dirichletVectorLowerOrder hK B C u k : L2) =
      ∑ i, schwartzMultiplier χ (dirichletLowerOrder hK (B k i) (C k i) (u i) : L2) := by
    rw [dirichletVectorLowerOrder_coe hK B C u k, map_sum]
  exact ⟨_, weakSchwartzDerivative_congr he hsum⟩

end PoincareConjecture.M35.Uniqueness.Heat
