import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.OrdinaryRealization.Slices

/-!
# Product topology for the ordinary generalized realization

Morgan-Tian, Theorem 12.28, printed pp. 323-324, through the Chapter 11
flow-box representation. The dependent sum of retained slices receives
the ordinary spacetime product topology, rather than a disjoint-union topology.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M35.OrdinaryRealization

/-- The retained dependent sum is the ordinary time interval times the original space.
Used in Theorem 12.28, pp. 323-324. -/
def spacetimeEquiv (J : Set ℝ) :
    (Σ t : ℝ, (slice J t).carrier) ≃ J × StandardCapSpace where
  toFun p := (⟨p.1, p.2.property⟩, p.2.val)
  invFun p := ⟨p.1.val, ⟨p.2, p.1.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The Chapter 11 realization uses the topology of the actual time product.
Used in Theorem 12.28, pp. 323-324. -/
@[instance_reducible]
def spacetimeTopology (J : Set ℝ) : TopologicalSpace (Σ t : ℝ, (slice J t).carrier) :=
  TopologicalSpace.induced (spacetimeEquiv J) inferInstance

/-- The single global flow box is a homeomorphism onto the retained spacetime.
Used in Theorem 12.28, pp. 323-324. -/
def spacetimeHomeomorph (J : Set ℝ) :
    letI := spacetimeTopology J
    (Σ t : ℝ, (slice J t).carrier) ≃ₜ J × StandardCapSpace :=
  letI := spacetimeTopology J
  (spacetimeEquiv J).toHomeomorphOfIsInducing ⟨rfl⟩

/-- The actual clock is continuous in the product topology.
Used in Theorem 12.28, pp. 323-324. -/
theorem time_continuous (J : Set ℝ) :
    letI := spacetimeTopology J
    Continuous (Sigma.fst : (Σ t : ℝ, (slice J t).carrier) → ℝ) := by
  let : TopologicalSpace (Σ t : ℝ, (slice J t).carrier) := spacetimeTopology J
  exact continuous_subtype_val.comp (continuous_fst.comp (spacetimeHomeomorph J).continuous)

/-- Each slice carries exactly the topology inherited from the ordinary manifold.
Used in Theorem 12.28, pp. 323-324. -/
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

end PoincareMT.M35.OrdinaryRealization
