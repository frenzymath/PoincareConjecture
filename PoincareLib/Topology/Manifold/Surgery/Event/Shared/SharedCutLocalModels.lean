import PoincareLib.Topology.Manifold.Surgery.Event.Full.FullCutLocalModels

/-!
# Restricting a local smooth map to its actual open target

The inverse open-region coordinates use the point under study as their
only fallback. The resulting local property keeps the literal subtype map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology Filter
open scoped Manifold ContDiff

universe u v

namespace PoincareMT.M38

/-- A map into an inherited open submanifold is locally a diffeomorphism whenever
its actual ambient composite is, with no extra nonemptiness assumption. -/
theorem openCodomain_localDiffeomorphAt
    (A : GeneralizedSliceCarrier.{u}) (U : TopologicalSpace.Opens A.carrier)
    {X : Type v} [TopologicalSpace X] [ChartedSpace StandardCapSpace X]
    (f : X → U) (x : X)
    (h : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (Subtype.val ∘ f) x) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ f x := by
  let e := openRegionEquivalence A U (f x)
  let d := regionPartialDiffeomorph e isOpen_univ U.isOpen
  have hi : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ d.symm (f x).val :=
    ⟨d.symm, (f x).property, fun _ _ => rfl⟩
  have hc := h.comp (𝓡 3) U hi
  apply hc.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun y => (e.left_inverse (Set.mem_univ (f y))).symm)

end PoincareMT.M38
