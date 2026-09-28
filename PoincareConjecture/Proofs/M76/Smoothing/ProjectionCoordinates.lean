import PoincareConjecture.Proofs.M76.Mathlib.TransverseAffineProjection
import PoincareConjecture.Proofs.M76.Smoothing.AtlasConstruction











set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture.M76

variable {ι M E : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem exists_smooth_atlas_of_transverse_coordinates
    (c : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source)
    (a : ι → EuclideanSpace ℝ (Fin 3) →ᴬ[ℝ] E)
    (P : ι → E → E →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hP : ∀ i x, x ∈ (c i).target → ContDiffAt ℝ ∞ (P i) (a i x))
    (htrans : ∀ i j x, x ∈ ((c i).symm.trans (c j)).source →
      ((P i (a i x)).comp (a j).contLinear).IsInvertible)
    (hleaf : ∀ i j x, x ∈ ((c i).symm.trans (c j)).source →
      P i (a i x) (a j (((c i).symm.trans (c j)) x) - a i x) = 0) :
    ∃ atlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      letI := atlas; IsManifold (𝓡 3) ∞ M := by
  apply exists_smooth_atlas_of_coordinates c hcover
  intro i j
  have hreg : ContDiffOn ℝ ∞
      (fun x => (a j).transverseCoordinates (P i (a i x)) (a i x))
      ((c i).symm.trans (c j)).source := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    exact (a j).contDiffAt_transverseCoordinates
      ((hP i x hx.1).comp x (a i).contDiff.contDiffAt)
      (a i).contDiff.contDiffAt (htrans i j x hx)
  apply hreg.congr
  intro x hx
  exact ((a j).transverseCoordinates_eq_iff (P i (a i x))
    (htrans i j x hx) (a i x) _).mpr (hleaf i j x hx) |>.symm

end PoincareConjecture.M76
