import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.CollarGluing.CollarOpenSides
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.CollarGluing.CollapseInjection
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.OriginalBoundaryProduct

/-! # The open-side cover of an original compact PL domain -/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

/-- Construct the actual open-side cover and simultaneous collapse directly
from the compact original PL domain and compact exterior. -/
theorem PLDomain.nonempty_openFrontierCollapse
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hminus : IsCompact (interior R)ᶜ)
    (hne : (interior R).Nonempty) (hneminus : (interior (interior R)ᶜ).Nonempty) :
    Nonempty (OpenFrontierCollapse R) := by
  obtain ⟨s, L, HB, c, hL, hc, hi, hbase, hmarks,
    delta, hdelta, hdeltaHalf, hcU, hopen⟩ :=
    he.exists_small_boundary_product_of_interiors_nonempty
      hR hminus hne hneminus isOpen_univ (subset_univ _)
  exact nonempty_openFrontierCollapse_of_bicollar he.closed
    (L.isCompact_space_of_finite hL) HB c hc.continuousOn hi hbase hmarks
    hdelta (by linarith) hopen

end PoincareMT.M76
