import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.Cylinder
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.GeneralizedFlowCylinder

variable {F : GeneralizedRicciFlowData.{u}} {C C' : GeneralizedSliceCarrier.{u}}
  {a q : ℝ} {I : Set ℝ} {U : Set C.carrier}
  (e : GeneralizedFlowCylinder F C a q I U)
  (f : C'.carrier → C.carrier) (g : C.carrier → C'.carrier)
  (hf : Topology.IsEmbedding f) (hfsmooth : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
  (hgsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g (range f))
  (hleft : Function.LeftInverse g f)

noncomputable def rebaseSourceEmbedding :
    GeneralizedFlowCylinder F C' a q I (f ⁻¹' U) := by
  have hmaps : MapsTo f (f ⁻¹' U) U := fun _ hx => hx
  have himage (s : ℝ) (hs : s ∈ I) :
      (e.forward s hs ∘ f) '' (f ⁻¹' U) ⊆ e.forward s hs '' U := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨f x, hx, rfl⟩
  refine {
    scale_pos := e.scale_pos
    forward := fun s hs => e.forward s hs ∘ f
    inverse := fun s hs => g ∘ e.inverse s hs
    forward_smooth := fun s hs => (e.forward_smooth s hs).comp hfsmooth.contMDiffOn hmaps
    inverse_smooth := ?_
    left_inverse := ?_
    right_inverse := ?_
    embedding := e.embedding.comp
      (Topology.IsEmbedding.id.prodMap (hf.restrict hmaps))
    vertical_compatibility := fun s hs x hx => e.vertical_compatibility s hs (f x) hx }
  · intro s hs
    apply hgsmooth.comp ((e.inverse_smooth s hs).mono (himage s hs))
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, (e.left_inverse s hs hx).symm⟩
  · intro s hs x hx
    dsimp only [Function.comp_apply]
    rw [e.left_inverse s hs hx, hleft]
  · intro s hs y hy
    obtain ⟨x, hx, rfl⟩ := hy
    dsimp only [Function.comp_apply]
    rw [e.left_inverse s hs hx, hleft]

theorem rebaseSourceEmbedding_pointMap (s : ℝ) (hs : s ∈ I) (x : C'.carrier) :
    (e.rebaseSourceEmbedding f g hf hfsmooth hgsmooth hleft).pointMap s hs x =
      e.pointMap s hs (f x) := rfl

theorem rebaseSourceEmbedding_pullbackInner (hU : IsOpen U) (s : ℝ) (hs : s ∈ I)
    (x : C'.carrier) (hx : f x ∈ U) (v w : TangentSpace (𝓡 3) x) :
    (e.rebaseSourceEmbedding f g hf hfsmooth hgsmooth hleft).pullbackInner s hs x v w =
      e.pullbackInner s hs (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) := by
  have he := ((e.forward_smooth s hs).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt
    (by simp)
  have hfd := hfsmooth.mdifferentiable (by simp) x
  dsimp only [pullbackInner, rebaseSourceEmbedding]
  rw [mfderiv_comp x he hfd]
  rfl

end PoincareConjecture.GeneralizedFlowCylinder
