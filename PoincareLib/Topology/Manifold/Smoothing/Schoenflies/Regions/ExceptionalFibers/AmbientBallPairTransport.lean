import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.UnitBallPairs
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Transport compact ball pairs with their complete ambient frontiers

The actual ambient open partial homeomorphism supplies the frontier
correspondence. A homeomorphism of bare closed cells is not used to
infer any ambient boundary statement. See Brown1960 Theorem3 and
Brown derivation017, section4.
-/

set_option autoImplicit false

open Set

namespace OpenPartialHomeomorph

variable {E X Y : Type*} [NormedAddCommGroup E]
  [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

/-- Move an actual compact ball pair through an ambient open partial
homeomorphism, preserving its whole ambient frontier.
See Brown derivation017, section4. -/
theorem image_compact_ballPair (e : OpenPartialHomeomorph X Y)
    {Q : Set X} (hQ : IsCompact Q) (hQs : Q ⊆ e.source)
    (hpair : IsUnitBallPair E Q (frontier Q)) :
    IsCompact (e '' Q) ∧ IsUnitBallPair E (e '' Q) (frontier (e '' Q)) := by
  have hcompact : IsCompact (e '' Q) :=
    hQ.image_of_continuousOn (e.continuousOn.mono hQs)
  have himage : e.IsImage Q (e '' Q) := by
    intro x hx
    constructor
    · rintro ⟨z, hz, he⟩
      exact (e.injOn (hQs hz) hx he) ▸ hz
    · intro hxQ
      exact ⟨x, hxQ, rfl⟩
  let H : Q ≃ₜ (e '' Q) := e.homeomorphOfImageSubsetSource hQs rfl
  refine ⟨hcompact, hpair.of_homeomorph hcompact.isClosed.frontier_subset H.symm ?_⟩
  intro y
  have hf := himage.frontier (hQs (H.symm y).property)
  have hv : e (H.symm y) = (y : Y) :=
    congrArg Subtype.val (H.apply_symm_apply y)
  rwa [hv] at hf

end OpenPartialHomeomorph
