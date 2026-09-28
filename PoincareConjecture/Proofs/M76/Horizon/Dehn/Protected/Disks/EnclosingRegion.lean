import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Disks.Construction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Regions.DiskSphereCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Regions.EnclosingRegion

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.ProtectedDisks

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

theorem nonempty_enclosing_region
    (L : Submodule ℤ V1) [DiscreteTopology L] {α : Type*}
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 2) (Fin 1) L) V3}
    (T : HamiltonProtectedDehnDisks L e)
    (he : PLDomain e (latticeHandleDomain (Fin 2) (Fin 1) L))
    (h : OpenPartialHomeomorph (V2 × V1) V3)
    (hsource : D2 ×ˢ (univ : Set V1) ⊆ h.source)
    {N : Set (V2 × V1)} (hboundary : frontier (D2 ×ˢ (univ : Set V1)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N))
    (retained : HamiltonRetainedBlockChart (Fin 2) (Fin 1) L e h) :
    Nonempty (HamiltonDehnEnclosingRegion (Fin 2) (Fin 1) L e (⋃ b, T.surface b)) := by
  obtain ⟨U, hU, hbounded, hfront, hfrontClosure⟩ :=
    exists_source_bounded_side L T retained he hsource N hboundary hPL
  have himage : hamiltonMarkedProjection (Fin 2) (Fin 1) L '' sourceProtectedDisks L T =
      ⋃ b, T.surface b := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨b, hb⟩ := mem_iUnion.mp hy
      obtain ⟨x, hx, rfl⟩ := (T.inside b hb).1
      exact ⟨x, ⟨hx, mem_iUnion.mpr ⟨b, hb⟩⟩, rfl⟩
  obtain ⟨s⟩ := T.nonempty_chartwisePLSphere he h hsource N hboundary hPL retained
  have hs : ChartwisePLSphere e
      ((hamiltonMarkedProjection (Fin 2) (Fin 1) L '' sourceProtectedDisks L T) ∪
        hamiltonAttachingBlock (Fin 2) (Fin 1) L (3 / 2)) := himage.symm ▸ s
  have hregion := nonempty_enclosing_region_of_source_side L e retained hU hbounded
    (sourceProtectedDisks_isCompact L T retained hsource).isClosed
    (sourceProtectedDisks_inside L T) (sourceProtectedDisks_outer_open L T retained)
    (sourceProtectedDisks_old_boundary L T retained)
    (hfront.trans (sourceSphere_decomposition L T retained))
    (hfrontClosure.trans hfront.symm) hs
  rwa [himage] at hregion

end PoincareConjecture.M76.Dehn.ProtectedDisks

namespace PoincareConjecture.M76

theorem hasHamiltonProtectedDehnDisks
    (L : Submodule ℤ (Fin 1 → ℝ)) [DiscreteTopology L] {α : Type*}
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 2) (Fin 1) L) (Fin 3 → ℝ)) :
    HasHamiltonProtectedDehnDisks L e := by
  intro he h hsource N _hN hboundary hPL hretained
  obtain ⟨retained⟩ := hretained
  obtain ⟨T, _, _⟩ := Dehn.ProtectedDisks.exists_protected_disk_pair
    L e he h hsource hboundary hPL retained
  exact ⟨T, Dehn.ProtectedDisks.nonempty_enclosing_region
    L T he h hsource hboundary hPL retained⟩

end PoincareConjecture.M76
