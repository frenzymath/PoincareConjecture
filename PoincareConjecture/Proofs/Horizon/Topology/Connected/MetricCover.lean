import Mathlib.Topology.Connected.Clopen
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Choose







set_option autoImplicit false

open Set Function

namespace Poincare.Topology


theorem components_card_le_of_image_ball_cover
    {X Y ι : Type*} [TopologicalSpace X] [PseudoMetricSpace Y] [Finite ι]
    (f : X → Y) (q : ι → Y) {r : ℝ}
    (hcover : ∀ x : X, ∃ i, dist (f x) (q i) < r)
    (hlocal : ∀ x y : X, dist (f x) (f y) < 2 * r → x ∈ connectedComponent y) :
    Finite (ConnectedComponents X) ∧
      Nat.card (ConnectedComponents X) ≤ Nat.card ι := by
  classical
  choose rep hrep using (ConnectedComponents.surjective_coe (α := X))
  choose index hindex using fun c : ConnectedComponents X => hcover (rep c)
  have hinj : Injective index := by
    intro c d hcd
    have hdist : dist (f (rep c)) (f (rep d)) < 2 * r := by
      have htri := dist_triangle (f (rep c)) (q (index c)) (f (rep d))
      have hc := hindex c
      have hd := hindex d
      rw [hcd, dist_comm (q (index d)) (f (rep d))] at htri
      rw [hcd] at hc
      simpa only [two_mul] using htri.trans_lt (add_lt_add hc hd)
    have heq := ConnectedComponents.coe_eq_coe'.mpr (hlocal (rep c) (rep d) hdist)
    simpa only [hrep] using heq
  exact ⟨Finite.of_injective index hinj, Nat.card_le_card_of_injective index hinj⟩

end Poincare.Topology
