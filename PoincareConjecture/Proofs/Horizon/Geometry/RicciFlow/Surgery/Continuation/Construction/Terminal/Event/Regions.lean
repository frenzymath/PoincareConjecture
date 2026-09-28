import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Retention







set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryRegionEquivalence

variable {A B C : GeneralizedSliceCarrier.{u}}
  {U : Set A.carrier} {V : Set B.carrier} {W : Set C.carrier}

def restrict (e : SurgeryRegionEquivalence A B U V) (S : Set A.carrier) (hS : S ⊆ U) :
    SurgeryRegionEquivalence A B S (e.map '' S) where
  map := e.map
  inverse := e.inverse
  map_image := rfl
  inverse_image := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa only [e.left_inverse (hS hy)] using hy
    · intro hx
      exact ⟨e.map x, mem_image_of_mem _ hx, e.left_inverse (hS hx)⟩
  left_inverse := fun _ hx => e.left_inverse (hS hx)
  right_inverse := fun _ hx => e.right_inverse (e.map_image ▸ image_mono hS hx)
  map_smooth := e.map_smooth.mono hS
  inverse_smooth := e.inverse_smooth.mono (by
    rintro _ ⟨x, hx, rfl⟩
    exact e.mapsTo (hS hx))

def trans (e : SurgeryRegionEquivalence A B U V) (f : SurgeryRegionEquivalence B C V W) :
    SurgeryRegionEquivalence A C U W where
  map := f.map ∘ e.map
  inverse := e.inverse ∘ f.inverse
  map_image := by rw [image_comp, e.map_image, f.map_image]
  inverse_image := by rw [image_comp, f.inverse_image, e.inverse_image]
  left_inverse := by
    intro x hx
    simp only [Function.comp_apply, f.left_inverse (e.mapsTo hx), e.left_inverse hx]
  right_inverse := by
    intro x hx
    change f.map (e.map (e.inverse (f.inverse x))) = x
    have he : e.map (e.inverse (f.inverse x)) = f.inverse x :=
      e.right_inverse (f.symm.mapsTo hx)
    rw [he]
    exact f.right_inverse hx
  map_smooth := f.map_smooth.comp e.map_smooth e.mapsTo
  inverse_smooth := e.inverse_smooth.comp f.inverse_smooth f.symm.mapsTo

theorem image_frontier (e : SurgeryRegionEquivalence A B U V)
    (hU : IsClosed U) (hV : IsClosed V) : e.map '' frontier U = frontier V := by
  rw [frontier, frontier, hU.closure_eq, hV.closure_eq]
  apply Subset.antisymm
  · rintro _ ⟨x, ⟨hx, hxi⟩, rfl⟩
    refine ⟨e.mapsTo hx, ?_⟩
    intro hi
    have h := e.symm.mapsTo_interior hi
    apply hxi
    simpa only [symm, e.left_inverse hx] using h
  · rintro y ⟨hy, hyi⟩
    refine ⟨e.inverse y, ⟨e.symm.mapsTo hy, ?_⟩, e.right_inverse hy⟩
    intro hi
    have h := e.mapsTo_interior hi
    exact hyi (e.right_inverse hy ▸ h)

end PoincareConjecture.SurgeryRegionEquivalence
