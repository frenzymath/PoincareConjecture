import PoincareConjecture.Proofs.M35.Uniqueness.Heat.InteriorFirstProducts









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem exists_weak_derivative_localized_source (K : Set V)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (χ : 𝓢(V, ℝ))
    (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K)
    (u : dirichletForm K) (hu : HasInteriorSecondDerivatives K u) (G Gk : L2) (k : Fin n)
    (hG : HasWeakSchwartzDerivative (schwartzMultiplier χ G) Gk
      (EuclideanSpace.single k (1 : ℝ))) :
    ∃ d : L2, HasWeakSchwartzDerivative (localizedDivergenceSource K A χ u G) d
      (EuclideanSpace.single k (1 : ℝ)) := by
  have hχd (i : Fin n) : HasCompactSupport
      ((∂_{EuclideanSpace.single i (1 : ℝ)} χ : 𝓢(V, ℝ)) : V → ℝ) :=
    hχ.of_isClosed_subset (isClosed_tsupport _) (SchwartzMap.tsupport_lineDerivOp_subset _ _)
  have hχdK (i : Fin n) :
      tsupport ((∂_{EuclideanSpace.single i (1 : ℝ)} χ : 𝓢(V, ℝ)) : V → ℝ) ⊆ interior K :=
    (SchwartzMap.tsupport_lineDerivOp_subset _ _).trans hχK
  let term : Fin n → Fin n → L2 := fun i j =>
    schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} χ)
      (schwartzMultiplier (A i j) (dirichletPartial K i u)) +
    (schwartzMultiplier (schwartzProduct (A i j) (∂_{EuclideanSpace.single i (1 : ℝ)} χ))
      (dirichletPartial K j u) +
    schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)}
      (schwartzProduct (A i j) (∂_{EuclideanSpace.single i (1 : ℝ)} χ)))
      (dirichletInclusion K u : L2))
  have hterm (i j : Fin n) : ∃ d : L2,
      HasWeakSchwartzDerivative (term i j) d (EuclideanSpace.single k (1 : ℝ)) := by
    obtain ⟨d₁, hd₁⟩ := exists_weak_derivative_partial_product K u hu
      (schwartzProduct (∂_{EuclideanSpace.single j (1 : ℝ)} χ) (A i j))
      (hχd j).mul_right (tsupport_mul_subset_left.trans (hχdK j)) i k
    rw [schwartzMultiplier_product] at hd₁
    obtain ⟨d₂, hd₂⟩ := exists_weak_derivative_partial_product K u hu
      (schwartzProduct (A i j) (∂_{EuclideanSpace.single i (1 : ℝ)} χ))
      (hχd i).mul_left (tsupport_mul_subset_right.trans (hχdK i)) j k
    have hd₃ := (dirichletPartial_weak K u k).mul _ _ _
      (∂_{EuclideanSpace.single j (1 : ℝ)}
        (schwartzProduct (A i j) (∂_{EuclideanSpace.single i (1 : ℝ)} χ)))
    exact ⟨_, hd₁.add (hd₂.add hd₃)⟩
  choose d hd using hterm
  have hsum := HasWeakSchwartzDerivative.sum (fun i => ∑ j, term i j)
    (fun i => ∑ j, d i j) _ (fun i => HasWeakSchwartzDerivative.sum _ _ _ (hd i))
  exact ⟨_, weakSchwartzDerivative_sub hG hsum⟩

end PoincareConjecture.M35.Uniqueness.Heat
