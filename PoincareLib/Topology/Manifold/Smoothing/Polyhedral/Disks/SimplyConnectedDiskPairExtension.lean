import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Disks.SimplyConnectedDiskExtension
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.UnitBallPairs

/-!

# Continuous fillings of actual topological disk pairs

One compatible disk model identifies the complete original
boundary with the circle. Its simply connected filling returns
to the original disk with every prescribed boundary value.
See Hatcher's 3-manifold notes, Theorem 3.1, pp. 45--48,
Hamilton 1976, Lemma 2, pp. 64--66 and M76 derivation 270.
-/

set_option autoImplicit false

open Metric

namespace Set

/-- Every continuous boundary map of an actual topological
two-disk pair extends into a simply connected target, with
literal agreement on the complete original boundary.
See Hatcher Theorem 3.1 and M76 derivation 270. -/
theorem IsUnitBallPair.exists_continuous_disk_extension
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace Y] {S B : Set X}
    (hS : IsUnitBallPair ℂ S B) (f : C(B, Y)) :
    ∃ g : C(S, Y), ∀ x : B, g ⟨x, hS.1 x.property⟩ = f x := by
  obtain ⟨hBS, e, he⟩ := hS
  let a : B ≃ₜ Circle := e.restrictSubsets hBS sphere_subset_closedBall he
  obtain ⟨g, hg⟩ :=
    (f.comp ⟨a.symm, a.symm.continuous⟩).exists_closedDisk_extension_of_simplyConnected
  refine ⟨g.comp ⟨e, e.continuous⟩, ?_⟩
  intro x
  have hexa : e ⟨x, hBS x.property⟩ =
      ⟨a x, sphere_subset_closedBall (a x).property⟩ := Subtype.ext rfl
  change g (e ⟨x, hBS x.property⟩) = f x
  rw [hexa, hg]
  exact congrArg f (a.symm_apply_apply x)

end Set
