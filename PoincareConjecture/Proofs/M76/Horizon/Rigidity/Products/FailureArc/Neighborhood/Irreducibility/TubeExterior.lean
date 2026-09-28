import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Irreducibility.BoundaryRemoval
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.BoundaryAttachment
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.Domain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.TwoPortComponentCarriers
import PoincareConjecture.Proofs.M76.Wall.PLDomainLocalPathConnected
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem OriginalIntervalTube.isPLIrreducible_exterior
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (hI : IsPLIrreducible e R)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    IsPLIrreducible e (R \ U.map '' openTube r) :=
  hI.sdiff_of_preconnected_boundary_meeting
    (OriginalIntervalTube.plDomain_exterior U hR hI.1 hr hr1)
    (OriginalIntervalTube.isConnected_openTube_image U hr hr1.le).isPreconnected
    (OriginalIntervalTube.openTube_meets_frontier U hr hr1.le)

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior
