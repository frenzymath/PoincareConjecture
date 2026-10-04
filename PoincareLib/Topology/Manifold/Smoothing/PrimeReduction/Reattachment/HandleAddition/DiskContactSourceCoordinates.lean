import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Reattachment.HandleAddition.EssentialDiskMinimum
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallImages

/-!
# Contact counts under source coordinates

A source homeomorphism transports the actual contact carrier and hence its
intrinsic connected-component count. This permits the planar circle engine
to act on the original two-coordinate compression disk.
-/

set_option autoImplicit false
open Set Geometry Topology
namespace PoincareMT.M76

theorem contact_component_card_source_homeomorph
    {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (a : E ≃ₜ F) (A : Set E) (f : E → X) (S : Set X) :
    Nat.card (ConnectedComponents ((a '' A) ∩ (f ∘ a.symm) ⁻¹' S : Set F)) =
      Nat.card (ConnectedComponents (A ∩ f ⁻¹' S : Set E)) := by
  have hset : a '' (A ∩ f ⁻¹' S) = (a '' A) ∩ (f ∘ a.symm) ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨mem_image_of_mem a hx.1,by simpa using hx.2⟩
    · rintro ⟨⟨x,hx,rfl⟩,hy⟩
      exact ⟨x,⟨hx,by simpa using hy⟩,rfl⟩
  let H := (a.image (A ∩ f ⁻¹' S)).trans (Homeomorph.setCongr hset)
  let C := H.isQuotientMap.isCoinducing.connectedComponentsHomeomorph fun y => by
    have hfiber : H ⁻¹' {y} = {H.symm y} := by
      ext x
      exact H.toEquiv.eq_symm_apply.symm
    rw [hfiber]
    exact isConnected_singleton
  exact (Nat.card_congr C.toEquiv).symm

end PoincareMT.M76

