import PoincareConjecture.Definitions.M53SphereSeparation
import PoincareConjecture.Proofs.M53.Mathlib.EmbeddingComplement











set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M53

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]




theorem sphere_dense_compl (S : SmoothEmbeddedNullHomotopicSphere (M := M)) :
    Dense (Set.range S.sphere)ᶜ := by
  apply S.smooth_embedding.dense_compl_range
  simp




theorem sphere_complement_nonempty [Nonempty M]
    (S : SmoothEmbeddedNullHomotopicSphere (M := M)) :
    (Set.univ \ Set.range S.sphere).Nonempty := by
  simpa only [Set.compl_eq_univ_sdiff] using (sphere_dense_compl S).nonempty

end PoincareConjecture.Proofs.M53
