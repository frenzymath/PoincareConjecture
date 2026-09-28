import PoincareConjecture.Proofs.M09.ActionCongruence

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T a b : ℝ}

theorem isMinimizingBackwardLPath_iff_of_eqOn (q r : BackwardTimePath F T a b)
    (heq : Set.EqOn q.curve r.curve (Set.Icc a b)) :
    IsMinimizingBackwardLPath F T a b q ↔ IsMinimizingBackwardLPath F T a b r := by
  have hleft := heq (show a ∈ Set.Icc a b from ⟨le_rfl, q.ordered.le⟩)
  have hright := heq (show b ∈ Set.Icc a b from ⟨q.ordered.le, le_rfl⟩)
  have haction := backwardLLength_congr_Ioo F T a b q.ordered.le q.curve r.curve
    (heq.mono Set.Ioo_subset_Icc_self)
  constructor
  · intro hq c hca hcb
    rw [← haction]
    exact hq c (hca.trans hleft.symm) (hcb.trans hright.symm)
  · intro hr c hca hcb
    rw [haction]
    exact hr c (hca.trans hleft) (hcb.trans hright)

end PoincareConjecture.Proofs.M09
