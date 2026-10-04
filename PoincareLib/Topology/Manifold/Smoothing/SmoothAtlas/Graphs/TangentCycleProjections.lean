import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.TangentCylinderSpace
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.LeafFields.AmbientBasisTransversePlanes
import PoincareLib.Topology.Manifold.Smoothing.SmoothAtlas.Graphs.AmbientCycleOperators

/-!
# Contractible projections of cyclic tangent cylinders

The ambient cyclic-star projection calculation supplies the normal
factor of the tangent-cylinder decomposition. Hence adding any fixed
tangent space preserves contractibility in the actual operator
topology. See Cairns 1940, Section 4, pp. 800--801, Section 11,
p. 807, and M76 derivations 32--33.
-/

set_option autoImplicit false

open Set ContinuousLinearMap

namespace PoincareMT.M76.Smoothing

variable {E T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- Geometric injectivity and the radial coordinate condition give
the same normalized ambient cycle operators.
See Cairns pp. 799--801 and M76 derivations 32--33. -/
noncomputable def ambientCycleFrameEmbeddingHomeomorph (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    FrameEmbeddingSpace (V.subtypeL.comp (cycleFrameInclusion b))
      (V.subtype '' ((cyclicEdgeComplex n).basisRadialEmbedding b).cone.space) ≃ₜ
      AmbientCycleProjectionSpace n V b :=
  Homeomorph.setCongr (by
    ext Q
    exact and_congr Iff.rfl
      ((cyclicEdgeComplex n).isRadialEmbedding_iff_injOn_basisCone_subtype V b Q).symm)

/-- Normalized operators embedding the actual included cyclic star
form a contractible space.
See Cairns pp. 801, 807 and M76 derivations 32--33. -/
theorem contractible_ambientCycleFrameEmbeddingSpace (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    ContractibleSpace (FrameEmbeddingSpace (V.subtypeL.comp (cycleFrameInclusion b))
      (V.subtype '' ((cyclicEdgeComplex n).basisRadialEmbedding b).cone.space)) := by
  let := contractible_ambientCycleProjectionSpace n V b
  exact (ambientCycleFrameEmbeddingHomeomorph n V b).contractibleSpace

/-- Cyclic normal stars with any tangent factor have contractible
normalized cylinder-projection spaces. The source is the full
saturated cylinder, not a finite list of vertices.
See Cairns pp. 800--801, 807 and M76 derivation 33. -/
theorem contractible_tangentCycleEmbeddingSpace (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    ContractibleSpace (TangentCylinderEmbeddingSpace
      (V.subtypeL.comp (cycleFrameInclusion b))
      (V.subtype '' ((cyclicEdgeComplex n).basisRadialEmbedding b).cone.space) T) := by
  let := contractible_ambientCycleFrameEmbeddingSpace n V b
  exact contractible_tangentCylinderEmbeddingSpace _ _

end PoincareMT.M76.Smoothing
