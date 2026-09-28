import PoincareConjecture.Proofs.M76.Smoothing.ProjectionCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.NormalizedProjectionLeaves










set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture.M76

variable {ι M E : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem exists_smooth_atlas_of_leaf_coordinates
    (c : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source)
    (v : M → E) (P : M → Submodule ℝ E)
    (b : ι → EuclideanSpace ℝ (Fin 3) →ᴬ[ℝ] E)
    (Q : ι → E → E →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hQ : ∀ i z, z ∈ (c i).target → ContDiffAt ℝ ∞ (Q i) (b i z))
    (hspec : ∀ i y, y ∈ (c i).source →
      Function.RightInverse (b i).contLinear (Q i (v y)) ∧
        (Q i (v y)).ker = P y ∧ Q i (b i (c i y)) = Q i (v y) ∧
        b i (c i y) - v y ∈ P y) :
    ∃ atlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      letI := atlas; IsManifold (𝓡 3) ∞ M := by
  apply exists_smooth_atlas_of_transverse_coordinates c hcover b Q hQ
  · intro i j z hz
    have hi := hspec i ((c i).symm z) ((c i).map_target hz.1)
    have hj := hspec j ((c i).symm z) hz.2
    rw [(c i).right_inv hz.1] at hi
    apply ContinuousLinearMap.isInvertible_comp_of_ker_eq
      (Q i (b i z)) (Q j (v ((c i).symm z))) (b j).contLinear _ hj.1
    rw [hi.2.2.1, hi.2.1, hj.2.1]
  · intro i j z hz
    have hi := hspec i ((c i).symm z) ((c i).map_target hz.1)
    have hj := hspec j ((c i).symm z) hz.2
    rw [(c i).right_inv hz.1] at hi
    have hmem : b j (c j ((c i).symm z)) - b i z ∈ P ((c i).symm z) := by
      convert! (P ((c i).symm z)).sub_mem hj.2.2.2 hi.2.2.2 using 1
      abel
    rw [← hi.2.1, ← hi.2.2.1] at hmem
    exact hmem

end PoincareConjecture.M76
