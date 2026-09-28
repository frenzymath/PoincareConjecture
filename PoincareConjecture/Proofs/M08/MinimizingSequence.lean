import PoincareConjecture.Proofs.M08.ActionBounds
import PoincareConjecture.Proofs.M08.AdmissiblePaths
import Mathlib.Topology.Order.IsLUB








set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral Topology

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

def backwardActionValues {J : Set ℝ} (F : RicciFlow n M J)
    (T τ₁ τ₂ : ℝ) (p₁ p₂ : M) : Set ℝ :=
  {L | ∃ p : BackwardTimePath F T τ₁ τ₂,
    p.curve τ₁ = p₁ ∧ p.curve τ₂ = p₂ ∧
      backwardLLength F T τ₁ τ₂ p.curve = L}

theorem backwardActionValues_bddBelow {J : Set ℝ} {F : RicciFlow n M J}
    [T3Space M] {T τmax τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hτ₂ : τ₂ ≤ τmax) (p₁ p₂ : M) :
    BddBelow (backwardActionValues F T τ₁ τ₂ p₁ p₂) := by
  obtain ⟨K, _, hK⟩ := hcurvature.2
  refine ⟨-(Real.sqrt τ₂ * (n : ℝ) ^ 2 * K) * (τ₂ - τ₁), ?_⟩
  rintro L ⟨p, _, _, rfl⟩
  exact (backwardLLength_coercive hM04 p hτ₂ hK).1


theorem exists_backward_minimizing_sequence {J : Set ℝ} {F : RicciFlow n M J}
    [ConnectedSpace M] [T3Space M] {T τmax τ₁ τ₂ : ℝ}
    (hM04 : RicciFlowCurvatureTheory.{u}) (hT : T ∈ J)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hτ₁ : 0 ≤ τ₁) (hordered : τ₁ < τ₂) (hτ₂ : τ₂ ≤ τmax)
    (p₁ p₂ : M) :
    ∃ p : ℕ → BackwardTimePath F T τ₁ τ₂,
      (∀ k, (p k).curve τ₁ = p₁ ∧ (p k).curve τ₂ = p₂) ∧
      Antitone (fun k ↦ backwardLLength F T τ₁ τ₂ (p k).curve) ∧
      Filter.Tendsto (fun k ↦ backwardLLength F T τ₁ τ₂ (p k).curve)
        Filter.atTop (𝓝 (sInf (backwardActionValues F T τ₁ τ₂ p₁ p₂))) := by
  have hne : (backwardActionValues F T τ₁ τ₂ p₁ p₂).Nonempty := by
    obtain ⟨p, hp₁, hp₂⟩ := exists_backwardTimePath (F := F) hM04 hT hτ₁ hordered
      (fun τ hτ ↦ hwindow (backwardTime_mem_window hτ₁ hτ₂ hτ)) p₁ p₂
    exact ⟨backwardLLength F T τ₁ τ₂ p.curve, p, hp₁, hp₂, rfl⟩
  obtain ⟨c, hcmono, hclim, hc⟩ := exists_seq_tendsto_sInf hne
    (backwardActionValues_bddBelow hM04 hcurvature hτ₂ p₁ p₂)
  choose p hp₁ hp₂ hpval using hc
  refine ⟨p, fun k ↦ ⟨hp₁ k, hp₂ k⟩, ?_, ?_⟩
  · simpa only [hpval] using hcmono
  · simpa only [hpval] using hclim

end PoincareConjecture.M08
