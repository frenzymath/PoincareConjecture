import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.AlexanderRecursiveRecenter
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.GenericNonisolatedHeightSigns

/-!
# Hereditary height signs of complete Alexander profiles

Both strict approaches are required at every nonisolated
point of its own level section, including exceptional
heights. The condition is unchanged by recentering and is
supplied initially by separating actual vertex heights.
See Alexander 1924, pp. 6--8 and M76 derivations 269 and 276.
-/

set_option autoImplicit false

open Set

namespace Geometry.AlexanderSectionProfile

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Both strict height approaches at each nonisolated point
of its actual complete level section. Isolated births and
deaths are intentionally excluded. This condition does not
discard exceptional heights. See Alexander pp. 6--8 and
M76 derivations 269 and 276. -/
def HasNonisolatedHeightSigns (W : AlexanderSectionProfile E) : Prop :=
  ∀ x ∈ W.carrier,
    x ∈ closure ((W.carrier ∩ {y | W.height y = W.height x}) \ {x}) →
    x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
      x ∈ closure (W.carrier ∩ {y | W.height x < W.height y})

/-- Subtracting one constant changes neither a point's own
level section nor either strict height set. The same sign
condition therefore holds after recentering.
See Alexander p. 7 and M76 derivation 276. -/
theorem HasNonisolatedHeightSigns.recenter {W : AlexanderSectionProfile E}
    (hW : W.HasNonisolatedHeightSigns) (c : ℝ) :
    (W.recenter c).HasNonisolatedHeightSigns := by
  simpa only [HasNonisolatedHeightSigns, recenter_carrier, recenter_height_apply,
    sub_left_inj, sub_lt_sub_iff_right] using hW

/-- A complete profile on the literal carrier of a finite
complex has the hereditary sign condition if its height
separates the actual vertices. No purity or dimension is
needed by this sign supplier. See Alexander pp. 6--8 and
M76 derivation 276. -/
theorem hasNonisolatedHeightSigns_of_generic_complex (W : AlexanderSectionProfile E)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hWK : W.carrier = K.space) (hA : InjOn W.height K.vertices) :
    W.HasNonisolatedHeightSigns := by
  intro x _ hacc
  have haccK : x ∈ closure ((K.space ∩ {y | W.height y = W.height x}) \ {x}) := by
    simpa only [hWK] using hacc
  simpa only [hWK] using
    K.mem_both_height_closures_of_generic_nonisolated hK W.height hA haccK

end Geometry.AlexanderSectionProfile
