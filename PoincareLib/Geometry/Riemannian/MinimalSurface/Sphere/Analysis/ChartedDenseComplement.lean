import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Perfect

/-!
# Punctured neighborhoods in a charted space

Morgan-Tian Claim 18.12, printed pp. 426-427, omitted-pole derivation.
An isolated point in a charted space would give an isolated point in
its model. A perfect model therefore gives dense singleton complements.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M60

variable {H X : Type*} [TopologicalSpace H] [PerfectSpace H]
  [TopologicalSpace X] [ChartedSpace H X]

include H in
/-- Singleton complements are dense in a space modeled on a perfect
space. Source: MT Claim 18.12, pp. 426-427, omitted-pole derivation. -/
theorem dense_compl_singleton_of_charted (p : X) : Dense ({p}ᶜ : Set X) := by
  apply dense_compl_singleton_iff_not_open.mpr
  intro hp
  have h := (chartAt H p).isOpen_image_of_subset_source hp
    (singleton_subset_iff.mpr (mem_chart_source H p))
  exact not_isOpen_singleton (chartAt H p p) (by simpa only [image_singleton] using h)

end PoincareMT.M60
