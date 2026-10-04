import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coverings.CoveringLiftRelative
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coverings.CoveringProduct
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.LatticeDisplacement

/-!
# Bounded lifts over a lattice quotient

A homeomorphism of a compact parameter space times a torus,
homotopic to the identity relative to a parameter subset, has
a boundary-fixed, lattice-equivariant homeomorphic lift.
Compactness of a fundamental domain bounds its displacement
in the Euclidean factor. See Hamilton 1976, p. 67 and M76
derivation 89.
-/

set_option autoImplicit false

open Set

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace A] [CompactSpace A] [T2Space A]

/-- A relative identity homotopy on a compact-parameter torus
gives a deck-equivariant homeomorphic lift with uniformly
bounded Euclidean displacement. See Hamilton p. 67 and
M76 derivation 89. -/
theorem IsZLattice.exists_bounded_relative_homeomorph_lift
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (g : (A × (E ⧸ L.toAddSubgroup)) ≃ₜ (A × (E ⧸ L.toAddSubgroup)))
    (S : Set A)
    (H : (ContinuousMap.id (A × (E ⧸ L.toAddSubgroup))).HomotopyRel
      ⟨g, g.continuous⟩ (S ×ˢ univ)) :
    ∃ G : (A × E) ≃ₜ (A × E),
      (∀ y, ((G y).1, QuotientAddGroup.mk (G y).2) =
        g (y.1, QuotientAddGroup.mk y.2)) ∧
      (∀ y, y.1 ∈ S → G y = y) ∧
      (∀ a x z, z ∈ L → G (a, x + z) = ((G (a, x)).1, (G (a, x)).2 + z)) ∧
      ∃ C > 0, ∀ a x, ‖(G (a, x)).2 - x‖ ≤ C := by
  let q : E → E ⧸ L.toAddSubgroup := QuotientAddGroup.mk
  have hq : IsCoveringMap q :=
    (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm DiscreteTopology.isDiscrete).isCoveringMap
  let p : A × E → A × (E ⧸ L.toAddSubgroup) := Prod.map id q
  have hp : IsCoveringMap p := hq.id_prod
  obtain ⟨G, hGp, hGfixed, hGdeck, _⟩ := hp.exists_relative_homeomorph_lift g (S ×ˢ univ) H
  have hGequiv (a : A) (x z : E) (hz : z ∈ L) :
      G (a, x + z) = ((G (a, x)).1, (G (a, x)).2 + z) := by
    let d : C(A × E, A × E) :=
      ⟨fun y => (y.1, y.2 + z), continuous_fst.prodMk (continuous_snd.add continuous_const)⟩
    refine hGdeck d ?_ (a, x)
    funext y
    change (y.1, q (y.2 + z)) = (y.1, q y.2)
    refine Prod.ext rfl ?_
    exact QuotientAddGroup.eq_iff_sub_mem.mpr (by
      simpa only [add_sub_cancel_left, Submodule.mem_toAddSubgroup] using hz)
  refine ⟨G, hGp, fun y hy => hGfixed y ⟨hy, mem_univ _⟩, hGequiv, ?_⟩
  exact IsZLattice.exists_pos_displacement_bound_prod L (fun y => (G y).2)
    G.continuous.snd (fun a x z hz => congrArg Prod.snd (hGequiv a x z hz))
