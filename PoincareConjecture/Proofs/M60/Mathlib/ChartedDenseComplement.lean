import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Perfect









set_option autoImplicit false

open Set

namespace PoincareConjecture.M60

variable {H X : Type*} [TopologicalSpace H] [PerfectSpace H]
  [TopologicalSpace X] [ChartedSpace H X]

include H in


theorem dense_compl_singleton_of_charted (p : X) : Dense ({p}ᶜ : Set X) := by
  apply dense_compl_singleton_iff_not_open.mpr
  intro hp
  have h := (chartAt H p).isOpen_image_of_subset_source hp
    (singleton_subset_iff.mpr (mem_chart_source H p))
  exact not_isOpen_singleton (chartAt H p p) (by simpa only [image_singleton] using h)

end PoincareConjecture.M60
