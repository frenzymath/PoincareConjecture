import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ContinuousInteriorJets
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.LocalizedSourceSmooth









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative
  DeTurckDomainRegularityNative

variable {n : ℕ} {ι : Type*} [TopologicalSpace ι]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

private def localizedCorrectionTerm (K : Set V) (A : Fin n → Fin n → 𝓢(V, ℝ))
    (χ : 𝓢(V, ℝ)) (u : dirichletForm K) (i j : Fin n) : L2 :=
  schwartzMultiplier (A i j)
    (schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} χ) (dirichletPartial K i u)) +
  (schwartzMultiplier (A i j)
    (schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} χ) (dirichletPartial K j u)) +
  (schwartzMultiplier (A i j)
    (localizedDirichletValue K (orderedSchwartzDerivative [j, i] χ) u) +
  schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} (A i j))
    (localizedDirichletValue K (orderedSchwartzDerivative [i] χ) u)))

private theorem correctionProduct (A χ : 𝓢(V, ℝ)) (i j : Fin n) (v : L2) :
      schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)}
        (schwartzProduct A (∂_{EuclideanSpace.single i (1 : ℝ)} χ))) v =
      schwartzMultiplier A
        (schwartzMultiplier (orderedSchwartzDerivative [j, i] χ) v) +
      schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} A)
        (schwartzMultiplier (orderedSchwartzDerivative [i] χ) v) := by
  rw [lineDeriv_schwartzProduct]
  change schwartzMultiplierLinear (_ + _) v = _
  rw [map_add, add_apply]
  change schwartzMultiplier _ v + schwartzMultiplier _ v = _
  rw [schwartzMultiplier_product, schwartzMultiplier_product]
  rfl

private theorem localizedCorrection_expansion (K : Set V) (A : Fin n → Fin n → 𝓢(V, ℝ))
    (χ : 𝓢(V, ℝ)) (u : dirichletForm K) :
    localizedDivergenceSource K A χ u 0 = 0 - ∑ i, ∑ j, localizedCorrectionTerm K A χ u i j := by
  unfold localizedDivergenceSource
  rw [map_zero]
  apply congrArg (fun z : L2 => 0 - z)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg₂ (· + ·)
    (schwartzMultiplier_commute (∂_{EuclideanSpace.single j (1 : ℝ)} χ)
      (A i j) (dirichletPartial K i u))
    (congrArg₂ (· + ·)
      (schwartzMultiplier_product (A i j) (∂_{EuclideanSpace.single i (1 : ℝ)} χ)
        (dirichletPartial K j u))
      (correctionProduct (A i j) χ i j (dirichletInclusion K u)))

theorem hasContinuousWeakJet_localizedDivergenceCorrection
    (K : Set V) (A : ι → Fin n → Fin n → 𝓢(V, ℝ)) {s : ℕ}
    (hA : ∀ i j w, w.length ≤ s + 1 →
      Continuous (fun t => schwartzMultiplier (orderedSchwartzDerivative w (A t i j))))
    (χ : 𝓢(V, ℝ)) (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K)
    (u : ι → dirichletForm K) (hu : HasContinuousInteriorJets K u (s + 1)) :
    HasContinuousWeakJet (fun t => localizedDivergenceSource K (A t) χ (u t) 0) s := by
  have hχw (w : List (Fin n)) : HasCompactSupport (orderedSchwartzDerivative w χ) :=
    hχ.of_isClosed_subset (isClosed_tsupport _) (tsupport_orderedSchwartzDerivative_subset w χ)
  have hχwK (w : List (Fin n)) : tsupport (orderedSchwartzDerivative w χ) ⊆ interior K :=
    (tsupport_orderedSchwartzDerivative_subset w χ).trans hχK
  let term : Fin n → Fin n → ι → L2 :=
    fun i j t => localizedCorrectionTerm K (A t) χ (u t) i j
  have hterm (i j : Fin n) : HasContinuousWeakJet (term i j) s := by
    have hm (w : List (Fin n)) (hw : w.length ≤ s) :
        Continuous (fun t => schwartzMultiplier (orderedSchwartzDerivative w (A t i j))) :=
      hA i j w (hw.trans (Nat.le_succ s))
    have h₁ := (hu.partial_product (orderedSchwartzDerivative [j] χ)
      (hχw [j]) (hχwK [j]) i).mul (fun t => A t i j) hm
    have h₂ := (hu.partial_product (orderedSchwartzDerivative [i] χ)
      (hχw [i]) (hχwK [i]) j).mul (fun t => A t i j) hm
    have h₃ := ((hu (orderedSchwartzDerivative [j, i] χ) (hχw [j, i]) (hχwK [j, i])).mono
      (Nat.le_succ s)).mul (fun t => A t i j) hm
    have hmd (w : List (Fin n)) (hw : w.length ≤ s) : Continuous (fun t =>
        schwartzMultiplier (orderedSchwartzDerivative w
          (∂_{EuclideanSpace.single j (1 : ℝ)} (A t i j)))) := by
      simpa only [orderedSchwartzDerivative_append, orderedSchwartzDerivative] using
        hA i j (w ++ [j]) (by simp only [List.length_append, List.length_singleton]; omega)
    have h₄ := ((hu (orderedSchwartzDerivative [i] χ) (hχw [i]) (hχwK [i])).mono
      (Nat.le_succ s)).mul (fun t => ∂_{EuclideanSpace.single j (1 : ℝ)} (A t i j)) hmd
    exact h₁.add (h₂.add (h₃.add h₄))
  have hsum := (HasContinuousWeakJet.zero (ι := ι) (n := n) s).sub
    (HasContinuousWeakJet.sum _ (fun i => HasContinuousWeakJet.sum _ (hterm i)))
  have he (t : ι) : localizedDivergenceSource K (A t) χ (u t) 0 =
      0 - ∑ i, ∑ j, term i j t := localizedCorrection_expansion K (A t) χ (u t)
  simpa only [he] using hsum

end PoincareConjecture.M35.Uniqueness.Heat
