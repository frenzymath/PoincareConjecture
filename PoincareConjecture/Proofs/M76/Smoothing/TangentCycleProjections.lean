import PoincareConjecture.Proofs.M76.Mathlib.TangentCylinderSpace
import PoincareConjecture.Proofs.M76.Mathlib.AmbientBasisTransversePlanes
import PoincareConjecture.Proofs.M76.Smoothing.AmbientCycleOperators

set_option autoImplicit false

open Set ContinuousLinearMap

namespace PoincareConjecture.M76.Smoothing

variable {E T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup T] [NormedSpace ℝ T]

noncomputable def ambientCycleFrameEmbeddingHomeomorph (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    FrameEmbeddingSpace (V.subtypeL.comp (cycleFrameInclusion b))
      (V.subtype '' ((cyclicEdgeComplex n).basisRadialEmbedding b).cone.space) ≃ₜ
      AmbientCycleProjectionSpace n V b :=
  Homeomorph.setCongr (by
    ext Q
    exact and_congr Iff.rfl
      ((cyclicEdgeComplex n).isRadialEmbedding_iff_injOn_basisCone_subtype V b Q).symm)

theorem contractible_ambientCycleFrameEmbeddingSpace (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    ContractibleSpace (FrameEmbeddingSpace (V.subtypeL.comp (cycleFrameInclusion b))
      (V.subtype '' ((cyclicEdgeComplex n).basisRadialEmbedding b).cone.space)) := by
  let := contractible_ambientCycleProjectionSpace n V b
  exact (ambientCycleFrameEmbeddingHomeomorph n V b).contractibleSpace

theorem contractible_tangentCycleEmbeddingSpace (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    ContractibleSpace (TangentCylinderEmbeddingSpace
      (V.subtypeL.comp (cycleFrameInclusion b))
      (V.subtype '' ((cyclicEdgeComplex n).basisRadialEmbedding b).cone.space) T) := by
  let := contractible_ambientCycleFrameEmbeddingSpace n V b
  exact contractible_tangentCylinderEmbeddingSpace _ _

end PoincareConjecture.M76.Smoothing
