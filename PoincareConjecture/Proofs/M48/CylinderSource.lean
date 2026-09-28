import PoincareConjecture.Definitions.Ch11.BlowupLimits










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.GeneralizedFlowCylinder

variable {F : GeneralizedRicciFlowData.{u}}
  {C C' : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : Set ℝ} {U : Set C.carrier}
  (d : GeneralizedFlowCylinder F C a q J U)
  (f : Diffeomorph (𝓡 3) (𝓡 3) C'.carrier C.carrier ∞)

noncomputable def rebaseSource : GeneralizedFlowCylinder F C' a q J (f ⁻¹' U) := by
  have hmaps : MapsTo f (f ⁻¹' U) U := fun _ hx => hx
  have himage (s : ℝ) (hs : s ∈ J) :
      (d.forward s hs ∘ f) '' (f ⁻¹' U) ⊆ d.forward s hs '' U := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨f x, hx, rfl⟩
  refine {
    scale_pos := d.scale_pos
    forward := fun s hs => d.forward s hs ∘ f
    inverse := fun s hs => f.symm ∘ d.inverse s hs
    forward_smooth := fun s hs => (d.forward_smooth s hs).comp f.contMDiff.contMDiffOn hmaps
    inverse_smooth := fun s hs =>
      f.symm.contMDiff.comp_contMDiffOn ((d.inverse_smooth s hs).mono (himage s hs))
    left_inverse := ?_
    right_inverse := ?_
    embedding := d.embedding.comp
      (Topology.IsEmbedding.id.prodMap (f.toHomeomorph.isEmbedding.restrict hmaps))
    vertical_compatibility := fun s hs x hx => d.vertical_compatibility s hs (f x) hx }
  · intro s hs x hx
    dsimp only [Function.comp_apply]
    rw [d.left_inverse s hs hx, f.symm_apply_apply]
  · intro s hs y hy
    rcases hy with ⟨x, hx, rfl⟩
    dsimp only [Function.comp_apply]
    rw [d.left_inverse s hs hx, f.apply_symm_apply]

theorem rebaseSource_forward (s : ℝ) (hs : s ∈ J) (x : C'.carrier) :
    (d.rebaseSource f).forward s hs x = d.forward s hs (f x) := rfl

theorem rebaseSource_pointMap (s : ℝ) (hs : s ∈ J) (x : C'.carrier) :
    (d.rebaseSource f).pointMap s hs x = d.pointMap s hs (f x) := rfl

theorem rebaseSource_pullbackInner (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    (x : C'.carrier) (hx : f x ∈ U) (v w : TangentSpace (𝓡 3) x) :
    (d.rebaseSource f).pullbackInner s hs x v w =
      d.pullbackInner s hs (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) := by
  have hd := ((d.forward_smooth s hs).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt
    (by simp)
  have hf := f.contMDiff.mdifferentiable (by simp) x
  dsimp only [pullbackInner, rebaseSource]
  rw [mfderiv_comp x hd hf]
  rfl

end PoincareConjecture.GeneralizedFlowCylinder
