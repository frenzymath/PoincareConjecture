import PoincareLib.Topology.Manifold.Smoothing.Dehn.Annuli.Surgery.Retention.RawChart
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Annuli.Descent.Crossings.ProjectedChart

set_option autoImplicit false
open Set Topology

namespace PoincareMT.M76.Dehn.Annuli

/-- The constructed projected crossing yields literal relatively open
embedded source branches and a full raw crossing chart. -/
theorem nonempty_rawSourceCrossing_of_projected
    {E X Y ι : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {S : Set E}
    {d : E → Y} {p : Y → X} {R : Set X} {x y : E}
    (hd : IsEmbedding (fun z : S ↦ d z)) (hx : x ∈ S) (hy : y ∈ S)
    (hxy : p (d x) = p (d y)) (C : ProjectedSourceCrossing e p d S R x y) :
    Nonempty (RawSourceCrossing e (p ∘ d) S R x y) :=
  nonempty_rawSourceCrossing_of_twoBranchWindow d p hd hx hy hxy C.window C.chart
    C.labels C.point C.source C.compatible C.left_image C.right_image C.region

end PoincareMT.M76.Dehn.Annuli
