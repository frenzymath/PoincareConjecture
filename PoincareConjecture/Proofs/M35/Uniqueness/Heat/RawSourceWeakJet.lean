import PoincareConjecture.Proofs.M35.Uniqueness.Heat.LowerOrderWeakJet










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem exists_weak_derivative_raw_source
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {K : Set V} (hK : IsClosed K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (u w : PiLp 2 (fun _ : Fin n => dirichletForm K))
    (hu : ∀ k, HasInteriorSecondDerivatives K (u k))
    (χ : 𝓢(V, ℝ)) (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K)
    (k j : Fin n) :
    ∃ d : L2, HasWeakSchwartzDerivative
      (schwartzMultiplier χ (((rawLowerFormOperator D hK η hη u) k : L2) -
        (dirichletInclusion K (w k) : L2))) d (EuclideanSpace.single j (1 : ℝ)) := by
  obtain ⟨d, hd⟩ := exists_weak_derivative_localized_vector_lowerOrder hK
    (rawCutoffFirstComponent D η hη) (rawCutoffZeroComponent D η hη) u hu χ hχ hχK k j
  have hw := localizedDirichletPartial_weak K χ (w k) j
  have hs := weakSchwartzDerivative_sub hd hw
  refine ⟨_, weakSchwartzDerivative_congr ?_ hs⟩
  exact map_sub (schwartzMultiplier χ) _ _

end PoincareConjecture.M35.Uniqueness.Heat
