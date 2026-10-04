import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Circles.SpanningArcDisk
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLIntervalBoundary
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallConnected

/-! # Two marked ends select a unique spanning intersection interval -/

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareMT.M76.Dehn.Annuli

theorem exists_unique_interval_of_two_marked_points
    {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (pieces : κ → Set E) (Q : Set E) (a b : E) (hab : a ≠ b)
    (hdis : Pairwise (fun i j => Disjoint (pieces i) (pieces j)))
    (hends : (⋃ i, pieces i) ∩ Q = {a, b})
    (hmodels : ∀ i, IsFinitePLBallPair ℝ (pieces i) (pieces i ∩ Q) ∨
      ∃ (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧
        P.HasSimplicialEdges ∧ P.boundary ℝ = pieces i ∧ Disjoint (pieces i) Q) :
    ∃ i, IsFinitePLBallPair ℝ (pieces i) {a, b} ∧ pieces i ∩ Q = {a, b} ∧
      ∀ j, j ≠ i →
        ∃ (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧
          P.HasSimplicialEdges ∧ P.boundary ℝ = pieces j ∧ Disjoint (pieces j) Q := by
  have ha := hends.symm.subset (show a ∈ ({a, b} : Set E) from Or.inl rfl)
  obtain ⟨i, hai⟩ := mem_iUnion.mp ha.1
  have hball : IsFinitePLBallPair ℝ (pieces i) (pieces i ∩ Q) := by
    rcases hmodels i with hball | ⟨_, _, _, _, _, havoid⟩
    · exact hball
    · exact (Set.disjoint_left.mp havoid hai ha.2).elim
  have hpair : pieces i ∩ Q = {a, b} := by
    have hsub : pieces i ∩ Q ⊆ ({a, b} : Set E) := fun x hx =>
      hends.subset ⟨mem_iUnion.mpr ⟨i, hx.1⟩, hx.2⟩
    obtain ⟨u, v, huv, hbd⟩ := hball.exists_boundary_eq_pair
    apply Set.eq_of_subset_of_ncard_le hsub
    · rw [hbd, Set.ncard_pair huv, Set.ncard_pair hab]
  refine ⟨i, hpair ▸ hball, hpair, ?_⟩
  intro j hji
  have havoid : Disjoint (pieces j) Q := by
    apply Set.disjoint_left.mpr
    intro x hx hxQ
    have hxends : x ∈ ({a, b} : Set E) :=
      hends.subset ⟨mem_iUnion.mpr ⟨j, hx⟩, hxQ⟩
    exact Set.disjoint_left.mp (hdis hji) hx (hpair.symm.subset hxends).1
  rcases hmodels j with hj | hpoly
  · obtain ⟨u, v, _, huv⟩ := hj.exists_boundary_eq_pair
    have hh : u ∈ pieces j ∩ Q := huv.symm.subset (Or.inl rfl)
    exact (Set.disjoint_left.mp havoid hh.1 hh.2).elim
  · exact hpoly

end PoincareMT.M76.Dehn.Annuli
