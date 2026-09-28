import PoincareConjecture.Proofs.M35.Thm12_28.Slices









set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization



def spacetimeEquiv (J : Set ℝ) :
    (Σ t : ℝ, (slice J t).carrier) ≃ J × StandardCapSpace where
  toFun p := (⟨p.1, p.2.property⟩, p.2.val)
  invFun p := ⟨p.1.val, ⟨p.2, p.1.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl



@[instance_reducible]
def spacetimeTopology (J : Set ℝ) : TopologicalSpace (Σ t : ℝ, (slice J t).carrier) :=
  TopologicalSpace.induced (spacetimeEquiv J) inferInstance



def spacetimeHomeomorph (J : Set ℝ) :
    letI := spacetimeTopology J
    (Σ t : ℝ, (slice J t).carrier) ≃ₜ J × StandardCapSpace :=
  letI := spacetimeTopology J
  (spacetimeEquiv J).toHomeomorphOfIsInducing ⟨rfl⟩



theorem time_continuous (J : Set ℝ) :
    letI := spacetimeTopology J
    Continuous (Sigma.fst : (Σ t : ℝ, (slice J t).carrier) → ℝ) := by
  let : TopologicalSpace (Σ t : ℝ, (slice J t).carrier) := spacetimeTopology J
  exact continuous_subtype_val.comp (continuous_fst.comp (spacetimeHomeomorph J).continuous)



theorem slice_embedding (J : Set ℝ) (t : ℝ) :
    letI := spacetimeTopology J
    Topology.IsEmbedding
      (fun x : (slice J t).carrier => (⟨t, x⟩ : Σ s : ℝ, (slice J s).carrier)) := by
  let : TopologicalSpace (Σ t : ℝ, (slice J t).carrier) := spacetimeTopology J
  by_cases ht : t ∈ J
  · apply (spacetimeHomeomorph J).isEmbedding.of_comp_iff.mp
    exact (isEmbedding_prodMkRight (⟨t, ht⟩ : J)).comp
      (sliceDiffeomorph ht).toHomeomorph.isEmbedding
  · have : IsEmpty (slice J t).carrier := ⟨fun x => ht x.property⟩
    exact Topology.IsEmbedding.of_subsingleton _

end PoincareConjecture.M35.OrdinaryRealization
