import PoincareConjecture.Definitions.Ch11.SingularLimits














set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M32

variable {F : GeneralizedRicciFlowData.{u}}
  {C C' : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : Set ℝ} {U : Set C.carrier}




noncomputable def rebasePartialCylinderSource
    (d : GeneralizedFlowCylinder F C a q J U)
    (e : OpenPartialHomeomorph C'.carrier C.carrier) (heU : e.target ⊆ U)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target) :
    GeneralizedFlowCylinder F C' a q J e.source := by
  have hmaps : MapsTo e e.source U := fun _ hx => heU (e.map_source hx)
  refine {
    scale_pos := d.scale_pos
    forward := fun s hs => d.forward s hs ∘ e
    inverse := fun s hs => e.symm ∘ d.inverse s hs
    forward_smooth := fun s hs => (d.forward_smooth s hs).comp he hmaps
    inverse_smooth := ?_
    left_inverse := ?_
    right_inverse := ?_
    embedding := d.embedding.comp (Topology.IsEmbedding.id.prodMap
      ((Topology.IsEmbedding.inclusion heU).comp e.toHomeomorphSourceTarget.isEmbedding))
    vertical_compatibility := fun s hs x hx =>
      d.vertical_compatibility s hs (e x) (hmaps hx) }
  · intro s hs
    apply hei.comp ((d.inverse_smooth s hs).mono ?_) ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact mem_image_of_mem (d.forward s hs) (hmaps hx)
    · rintro _ ⟨x, hx, rfl⟩
      change d.inverse s hs (d.forward s hs (e x)) ∈ e.target
      rw [d.left_inverse s hs (hmaps hx)]
      exact e.map_source hx
  · intro s hs x hx
    dsimp only [Function.comp_apply]
    rw [d.left_inverse s hs (hmaps hx), e.left_inv hx]
  · intro s hs y hy
    obtain ⟨x, hx, rfl⟩ := hy
    dsimp only [Function.comp_apply]
    rw [d.left_inverse s hs (hmaps hx), e.left_inv hx]



theorem rebasePartialCylinderSource_pullbackInner
    (d : GeneralizedFlowCylinder F C a q J U)
    (e : OpenPartialHomeomorph C'.carrier C.carrier) (heU : e.target ⊆ U)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hU : IsOpen U) (s : ℝ) (hs : s ∈ J) (x : C'.carrier) (hx : x ∈ e.source)
    (v w : TangentSpace (𝓡 3) x) :
    (rebasePartialCylinderSource d e heU he hei).pullbackInner s hs x v w =
      d.pullbackInner s hs (e x) (mfderiv (𝓡 3) (𝓡 3) e x v)
        (mfderiv (𝓡 3) (𝓡 3) e x w) := by
  have hd := ((d.forward_smooth s hs).contMDiffAt
    (hU.mem_nhds (heU (e.map_source hx)))).mdifferentiableAt (by simp)
  have hef := (he.contMDiffAt (e.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  dsimp only [GeneralizedFlowCylinder.pullbackInner, rebasePartialCylinderSource]
  rw [mfderiv_comp x hd hef]
  rfl

end PoincareConjecture.M32
