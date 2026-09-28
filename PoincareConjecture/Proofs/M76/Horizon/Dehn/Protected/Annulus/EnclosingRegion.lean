import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Spheres.Annulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Regions.AnnulusSphereCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Regions.EnclosingRegion









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D1" => closedBall (0 : V1) 1

theorem nonempty_enclosing_region
    (L : Submodule ℤ V2) [DiscreteTopology L] {α : Type*}
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
    (T : HamiltonProtectedDehnAnnulus L e)
    (he : PLDomain e (latticeHandleDomain (Fin 1) (Fin 2) L))
    (h : OpenPartialHomeomorph (V1 × V2) V3)
    (hsource : D1 ×ˢ (univ : Set V2) ⊆ h.source)
    {N : Set (V1 × V2)} (hboundary : frontier (D1 ×ˢ (univ : Set V2)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N))
    (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h) :
    Nonempty (HamiltonDehnEnclosingRegion (Fin 1) (Fin 2) L e T.surface) := by
  obtain ⟨s⟩ := T.nonempty_chartwisePLSphere he h hsource N hboundary hPL retained
  obtain ⟨U, hU, hbounded, hfront, hfrontClosure⟩ :=
    exists_source_bounded_side L T retained he hsource s
  have himage := sourceProtectedAnnulus_projection L T
  have hs : ChartwisePLSphere e
      ((hamiltonMarkedProjection (Fin 1) (Fin 2) L '' sourceProtectedAnnulus L T) ∪
        hamiltonAttachingBlock (Fin 1) (Fin 2) L (3 / 2)) := himage.symm ▸ s
  have hregion := nonempty_enclosing_region_of_source_side L e retained hU hbounded
    (sourceProtectedAnnulus_isCompact L T).isClosed
    (sourceProtectedAnnulus_inside L T) (sourceProtectedAnnulus_outer_open L T retained)
    (sourceProtectedAnnulus_old_boundary L T retained)
    (hfront.trans (sourceSphere_decomposition L T retained))
    (hfrontClosure.trans hfront.symm) hs
  rwa [himage] at hregion

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
