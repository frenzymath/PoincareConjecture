import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ContinuousInteriorJets
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.HigherLowerOrder









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative
  DeTurckDomainRegularityNative

variable {n m : ℕ} {ι : Type*} [TopologicalSpace ι]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem hasContinuousWeakJet_localized_lowerOrder {K : Set V} (hK : IsClosed K)
    (B : ι → Fin n → 𝓢(V, ℝ)) (C : ι → 𝓢(V, ℝ)) {s : ℕ}
    (hB : ∀ i w, w.length ≤ s →
      Continuous (fun t => schwartzMultiplier (orderedSchwartzDerivative w (B t i))))
    (hC : ∀ w, w.length ≤ s →
      Continuous (fun t => schwartzMultiplier (orderedSchwartzDerivative w (C t))))
    (u : ι → dirichletForm K) (hu : HasContinuousInteriorJets K u (s + 1))
    (χ : 𝓢(V, ℝ)) (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K) :
    HasContinuousWeakJet (fun t =>
      schwartzMultiplier χ (dirichletLowerOrder hK (B t) (C t) (u t) : L2)) s := by
  have hfirst (i : Fin n) := (hu.partial_product χ hχ hχK i).mul (fun t => B t i) (hB i)
  have hzero := ((hu χ hχ hχK).mono (Nat.le_succ s)).mul C hC
  have hsum := (HasContinuousWeakJet.sum _ hfirst).add hzero
  have he (t : ι) :
      (∑ i, schwartzMultiplier (B t i) (schwartzMultiplier χ (dirichletPartial K i (u t)))) +
        schwartzMultiplier (C t) (localizedDirichletValue K χ (u t)) =
          schwartzMultiplier χ (dirichletLowerOrder hK (B t) (C t) (u t) : L2) := by
    simp only [dirichletLowerOrder_coe, map_add, map_sum, localizedDirichletValue]
    congr 1
    · exact Finset.sum_congr rfl (fun i _ => schwartzMultiplier_commute (B t i) χ _)
    · exact schwartzMultiplier_commute (C t) χ _
  simpa only [he] using hsum

theorem hasContinuousWeakJet_localized_vector_lowerOrder {K : Set V} (hK : IsClosed K)
    (B : ι → Fin m → Fin m → Fin n → 𝓢(V, ℝ))
    (C : ι → Fin m → Fin m → 𝓢(V, ℝ)) {s : ℕ}
    (hB : ∀ i j k w, w.length ≤ s →
      Continuous (fun t => schwartzMultiplier (orderedSchwartzDerivative w (B t i j k))))
    (hC : ∀ i j w, w.length ≤ s →
      Continuous (fun t => schwartzMultiplier (orderedSchwartzDerivative w (C t i j))))
    (u : ι → PiLp 2 (fun _ : Fin m => dirichletForm K))
    (hu : ∀ k, HasContinuousInteriorJets K (fun t => u t k) (s + 1))
    (χ : 𝓢(V, ℝ)) (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K) (k : Fin m) :
    HasContinuousWeakJet (fun t =>
      schwartzMultiplier χ (dirichletVectorLowerOrder hK (B t) (C t) (u t) k : L2)) s := by
  have hsum := HasContinuousWeakJet.sum _ (fun i => hasContinuousWeakJet_localized_lowerOrder
    hK (fun t => B t k i) (fun t => C t k i) (hB k i) (hC k i)
    (fun t => u t i) (hu i) χ hχ hχK)
  simpa only [dirichletVectorLowerOrder_coe, map_sum] using hsum

end PoincareConjecture.M35.Uniqueness.Heat
