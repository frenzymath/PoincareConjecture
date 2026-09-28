import PoincareConjecture.Proofs.M33.HistoryMetric

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {G : GeneralizedRicciFlowData.{u}} {F : SurgeryFlowData.{u}}
  (H : M33RegularHistoryRealization G F) (t : ℝ) (ht : t ∈ G.interval)
  (x : (G.slice t).carrier) (r : ℝ) {a q : ℝ} {J : Set ℝ}
  (d : GeneralizedFlowCylinder G (F.slice t) a q J
    ((F.metric t).ball (H.forward t ht x) r))

noncomputable def M33RegularHistoryRealization.rebaseCylinder :
    GeneralizedFlowCylinder G (G.slice t) a q J ((G.metric t).ball x r) := by
  have hmaps : MapsTo (H.forward t ht) ((G.metric t).ball x r)
      ((F.metric t).ball (H.forward t ht x) r) :=
    fun y hy => H.ball_image_subset t ht x r ⟨y, hy, rfl⟩
  have himage (s : ℝ) (hs : s ∈ J) :
      (d.forward s hs ∘ H.forward t ht) '' (G.metric t).ball x r ⊆
        d.forward s hs '' (F.metric t).ball (H.forward t ht x) r := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨H.forward t ht y, hmaps hy, rfl⟩
  refine {
    scale_pos := d.scale_pos
    forward := fun s hs => d.forward s hs ∘ H.forward t ht
    inverse := fun s hs => H.inverse t ht ∘ d.inverse s hs
    forward_smooth := fun s hs =>
      (d.forward_smooth s hs).comp (H.forward_smooth t ht).contMDiffOn hmaps
    inverse_smooth := ?_
    left_inverse := ?_
    right_inverse := ?_
    embedding := ?_
    vertical_compatibility := fun s hs y hy => d.vertical_compatibility s hs _ (hmaps hy)
  }
  · intro s hs
    apply (H.inverse_smooth t ht).comp ((d.inverse_smooth s hs).mono (himage s hs))
    rintro _ ⟨y, hy, rfl⟩
    change d.inverse s hs (d.forward s hs (H.forward t ht y)) ∈ range (H.forward t ht)
    rw [d.left_inverse s hs (hmaps hy)]
    exact ⟨y, rfl⟩
  · intro s hs y hy
    dsimp only [Function.comp_apply]
    rw [d.left_inverse s hs (hmaps hy), H.left_inverse t ht y]
  · intro s hs y hy
    rcases hy with ⟨z, hz, rfl⟩
    dsimp only [Function.comp_apply]
    rw [d.left_inverse s hs (hmaps hz), H.left_inverse t ht z]
  · exact d.embedding.comp
      (Topology.IsEmbedding.id.prodMap ((H.forward_openEmbedding t ht).isEmbedding.restrict hmaps))

theorem M33RegularHistoryRealization.rebaseCylinder_forward
    (s : ℝ) (hs : s ∈ J) (y : (G.slice t).carrier) :
    (H.rebaseCylinder t ht x r d).forward s hs y =
      d.forward s hs (H.forward t ht y) := rfl

end PoincareConjecture
