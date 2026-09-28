import PoincareConjecture.Definitions.Ch11.BlowupLimits








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.GeneralizedFlowCylinder

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {a q : ℝ} {J J' : Set ℝ} {U U' : Set C.carrier}
  (e : GeneralizedFlowCylinder F C a q J U) (hJ : J' ⊆ J) (hU : U' ⊆ U)

noncomputable def restrict : GeneralizedFlowCylinder F C a q J' U' where
  scale_pos := e.scale_pos
  forward := fun s hs => e.forward s (hJ hs)
  inverse := fun s hs => e.inverse s (hJ hs)
  forward_smooth := fun s hs => (e.forward_smooth s (hJ hs)).mono hU
  inverse_smooth := fun s hs => (e.inverse_smooth s (hJ hs)).mono (image_mono hU)
  left_inverse := fun s hs x hx => e.left_inverse s (hJ hs) (hU hx)
  right_inverse := fun s hs x hx => e.right_inverse s (hJ hs) (image_mono hU hx)
  embedding := e.embedding.comp ((Topology.IsEmbedding.inclusion hJ).prodMap
    (Topology.IsEmbedding.inclusion hU))
  vertical_compatibility := by
    intro s hs x hx
    obtain ⟨b, y, δ, hδ, h⟩ := e.vertical_compatibility s (hJ hs) x (hU hx)
    exact ⟨b, y, δ, hδ, fun s' hs' hnear => h s' (hJ hs') hnear⟩

theorem restrict_pointMap (s : ℝ) (hs : s ∈ J') (x : C.carrier) :
    (e.restrict hJ hU).pointMap s hs x = e.pointMap s (hJ hs) x := rfl

theorem restrict_pullbackInner (s : ℝ) (hs : s ∈ J') (x : C.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (e.restrict hJ hU).pullbackInner s hs x v w =
      e.pullbackInner s (hJ hs) x v w := rfl

end PoincareConjecture.GeneralizedFlowCylinder
