import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexThreeRegionSupplier
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateCylinder

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

def HasHamiltonChartHandleStraightening (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] (J : Finset (Fin 3)) : Prop :=
  ∀ e : OpenPartialHomeomorph (Fin 3 → ℝ) E,
    coordinateCylinder J ⊆ e.source →
    ∀ N : Set (Fin 3 → ℝ), IsOpen N → frontier (coordinateCylinder J) ⊆ N →
      LocallyPiecewiseAffineOn e (e.source ∩ N) →
      ∃ A : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
        FinitePiecewiseAffineOn (e ∘ A) (closedBall (0 : Fin 3 → ℝ) 1) ∧
        Nonempty (ContinuousMap.HomotopyWith
          (ContinuousMap.id (Fin 3 → ℝ)) ⟨A, A.continuous⟩
          (fun f => IsHomeomorph f ∧ (∀ x, 2 ≤ ‖x‖ → f x = x) ∧
            ∀ x ∈ (coordinateCylinder J)ᶜ ∪ frontier (coordinateCylinder J), f x = x))

theorem hasHamiltonChartHandleStraightening_of_zero_charge_and_lower_indices
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 3)
    (base : HasZeroChargeAlexanderRegionBalls E)
    (indexZero : HasHamiltonChartHandleStraightening E ∅)
    (indexOne : ∀ J : Finset (Fin 3), J.card = 1 → HasHamiltonChartHandleStraightening E J)
    (indexTwo : ∀ J : Finset (Fin 3), J.card = 2 → HasHamiltonChartHandleStraightening E J) :
    ∀ J : Finset (Fin 3), HasHamiltonChartHandleStraightening E J := by
  intro J
  classical
  have hcard : J.card ≤ 3 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ J)
  by_cases h0 : J.card = 0
  · have hJ := Finset.card_eq_zero.mp h0
    subst J
    exact indexZero
  by_cases h1 : J.card = 1
  · exact indexOne J h1
  by_cases h2 : J.card = 2
  · exact indexTwo J h2
  have h3 : J = Finset.univ :=
    Finset.eq_univ_of_card J (by simpa using (show J.card = 3 by omega))
  subst J
  have hcyl : coordinateCylinder (Finset.univ : Finset (Fin 3)) =
      closedBall (0 : Fin 3 → ℝ) 1 := by
    ext x
    simp only [coordinateCylinder, mem_ofPred_eq, Finset.mem_univ, forall_true_left,
      mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one, Real.norm_eq_abs]
  intro e hsource N _ hfront hPL
  rw [hcyl] at hsource hfront
  have hboundary : sphere (0 : Fin 3 → ℝ) 1 ⊆ e.source ∩ N := by
    intro x hx
    refine ⟨hsource (sphere_subset_closedBall hx), ?_⟩
    exact hfront ((frontier_closedBall _ one_ne_zero).symm.subset hx)
  obtain ⟨_, _, _, A, _, hA, _, ⟨H⟩⟩ :=
    exists_indexThree_chart_handleStraightening_of_zero_charge_supplier
      hdim base e hsource hPL hboundary
  refine ⟨A, hA, ⟨{ H.toHomotopy with prop' := ?_ }⟩⟩
  intro t
  refine ⟨(H.prop t).1, fun x hx => (H.prop t).2 x (by linarith), ?_⟩
  intro x hx
  apply (H.prop t).2 x
  rw [hcyl, frontier_closedBall _ one_ne_zero] at hx
  rcases hx with hx | hx
  · exact (not_le.mp (by simpa only [mem_compl_iff, mem_closedBall_zero_iff] using hx)).le
  · exact le_of_eq (mem_sphere_zero_iff_norm.mp hx).symm

end PoincareConjecture.M76
