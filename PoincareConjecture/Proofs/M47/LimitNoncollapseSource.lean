import PoincareConjecture.Proofs.M47.LimitNoncollapseClock
import PoincareConjecture.Proofs.M47.LimitRP2Charts

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

variable {F : GeneralizedRicciFlowData.{u}} {C B : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
  (e : GeneralizedFlowCylinder F C origin scale I U)
  (D : PartialDiffeomorph (𝓡 3) (𝓡 3) B.carrier C.carrier ∞)
  (V : Set B.carrier) (hV : V ⊆ D.source) (hmaps : MapsTo D V U)

noncomputable def limitNoncollapseCylinderSource :
    GeneralizedFlowCylinder F B origin scale I V := by
  have himage (s : ℝ) (hs : s ∈ I) :
      (e.forward s hs ∘ D) '' V ⊆ e.forward s hs '' U := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨D x, hmaps hx, rfl⟩
  refine {
    scale_pos := e.scale_pos
    forward := fun s hs => e.forward s hs ∘ D
    inverse := fun s hs => D.symm ∘ e.inverse s hs
    forward_smooth := fun s hs => (e.forward_smooth s hs).comp
      (D.contMDiffOn.mono hV) hmaps
    inverse_smooth := ?_
    left_inverse := ?_
    right_inverse := ?_
    embedding := ?_
    vertical_compatibility := fun s hs x hx => e.vertical_compatibility s hs _ (hmaps hx)
  }
  · intro s hs
    apply D.symm.contMDiffOn.comp ((e.inverse_smooth s hs).mono (himage s hs))
    rintro _ ⟨x, hx, rfl⟩
    change e.inverse s hs (e.forward s hs (D x)) ∈ D.target
    rw [e.left_inverse s hs (hmaps hx)]
    exact D.map_source (hV hx)
  · intro s hs x hx
    dsimp only [Function.comp_apply]
    rw [e.left_inverse s hs (hmaps hx)]
    exact D.left_inv (hV hx)
  · rintro s hs _ ⟨x, hx, rfl⟩
    dsimp only [Function.comp_apply]
    rw [e.left_inverse s hs (hmaps hx)]
    exact congrArg (fun z => e.forward s hs (D z)) (D.left_inv (hV hx))
  · have hd : Topology.IsEmbedding (fun x : V => D x.val) :=
      D.toOpenPartialHomeomorph.isEmbedding_restrict.comp
        (Topology.IsEmbedding.inclusion hV)
    exact e.embedding.comp (Topology.IsEmbedding.id.prodMap
      (hd.codRestrict U (fun x => hmaps x.property)))

theorem limitNoncollapseCylinderSource_pointMap (s : ℝ) (hs : s ∈ I)
    (x : B.carrier) :
    (limitNoncollapseCylinderSource e D V hV hmaps).pointMap s hs x =
      e.pointMap s hs (D x) := rfl

theorem limitNoncollapseCylinderSource_pullbackInner (hU : IsOpen U)
    (s : ℝ) (hs : s ∈ I) (x : B.carrier) (hx : x ∈ V)
    (v w : TangentSpace (𝓡 3) x) :
    (limitNoncollapseCylinderSource e D V hV hmaps).pullbackInner s hs x v w =
      e.pullbackInner s hs (D x)
        (mfderiv (𝓡 3) (𝓡 3) D x v) (mfderiv (𝓡 3) (𝓡 3) D x w) := by
  have he := ((e.forward_smooth s hs).mdifferentiableOn (by simp) _
    (hmaps hx)).mdifferentiableAt (hU.mem_nhds (hmaps hx))
  have hd := (D.contMDiffOn.mdifferentiableOn (by simp) _
    (hV hx)).mdifferentiableAt (D.open_source.mem_nhds (hV hx))
  change scale * (F.metric _).inner ((e.forward s hs ∘ D) x)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs ∘ D) x v)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs ∘ D) x w) = _
  rw [mfderiv_comp x he hd]
  rfl

end PoincareConjecture.M47
