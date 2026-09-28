import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Arcs.Mathlib.ShiftedCircleClosedArc
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Arcs.ComplementarySlabContraction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.ExactFrontierPreimage
import PoincareConjecture.Proofs.M76.Wall.OppositePLDomain










set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem circle_slab_closed_exterior_eq
    {X : Type*} [TopologicalSpace X] (p : ℝ) [Fact (0 < p)]
    (q : C(X, AddCircle p)) {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (hfront : frontier (q ⁻¹' AddCircle.closedIntervalArc p a b) =
      q ⁻¹' {(a : AddCircle p), (b : AddCircle p)}) :
    (interior (q ⁻¹' AddCircle.closedIntervalArc p a b))ᶜ =
      q ⁻¹' AddCircle.closedIntervalArc p b (a + p) := by
  have h : frontier (q ⁻¹' AddCircle.closedIntervalArc p a b) =
      q ⁻¹' frontier (AddCircle.closedIntervalArc p a b) := by
    rw [AddCircle.frontier_closedIntervalArc p ha hab.le hb]
    exact hfront
  rw [q.interior_preimage_of_frontier_eq h, ← preimage_compl,
    AddCircle.compl_interior_closedIntervalArc p ha hab hb]

theorem PLDomain.circle_slab_of_complementary
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (p : ℝ) [Fact (0 < p)] (q : C(X, AddCircle p))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (he : PLDomain e (q ⁻¹' AddCircle.closedIntervalArc p b (a + p)))
    (hfront : frontier (q ⁻¹' AddCircle.closedIntervalArc p b (a + p)) =
      q ⁻¹' {(a : AddCircle p), (b : AddCircle p)}) :
    PLDomain e (q ⁻¹' AddCircle.closedIntervalArc p a b) ∧
      frontier (q ⁻¹' AddCircle.closedIntervalArc p a b) =
        q ⁻¹' {(a : AddCircle p), (b : AddCircle p)} ∧
      (interior (q ⁻¹' AddCircle.closedIntervalArc p a b))ᶜ =
        q ⁻¹' AddCircle.closedIntervalArc p b (a + p) := by
  have htarget : frontier (AddCircle.closedIntervalArc p b (a + p)) =
      {(a : AddCircle p), (b : AddCircle p)} := by
    rw [AddCircle.frontier_closedIntervalArc_shifted p
      (c := (a + b) / 2) (by linarith) (by linarith) (by linarith),
      AddCircle.coe_add_period]
    exact pair_comm _ _
  have hpre : frontier (q ⁻¹' AddCircle.closedIntervalArc p b (a + p)) =
      q ⁻¹' frontier (AddCircle.closedIntervalArc p b (a + p)) := by
    rw [htarget]
    exact hfront
  have hreverse : (interior (AddCircle.closedIntervalArc p b (a + p)))ᶜ =
      AddCircle.closedIntervalArc p a b := by
    rw [← AddCircle.compl_interior_closedIntervalArc p ha hab hb,
      interior_compl, compl_compl]
    exact AddCircle.closure_interior_closedIntervalArc_shifted p (c := 0) ha hab
      (by simpa only [zero_add] using hb)
  have hdomain : (interior (q ⁻¹' AddCircle.closedIntervalArc p b (a + p)))ᶜ =
      q ⁻¹' AddCircle.closedIntervalArc p a b := by
    rw [q.interior_preimage_of_frontier_eq hpre, ← preimage_compl, hreverse]
  obtain ⟨he', hfront'⟩ := he.compl_interior
  rw [hdomain] at he' hfront'
  have hnewfront := hfront'.trans hfront
  exact ⟨he', hnewfront, circle_slab_closed_exterior_eq p q ha hab hb hnewfront⟩

end PoincareConjecture.M76
