import PoincareConjecture.Proofs.M76.Mathlib.SimplyConnectedDiskExtension
import PoincareConjecture.Proofs.M76.Mathlib.UnitBallPairs












set_option autoImplicit false

open Metric

namespace Set





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
