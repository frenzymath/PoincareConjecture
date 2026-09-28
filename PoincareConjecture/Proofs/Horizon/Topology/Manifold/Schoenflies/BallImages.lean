import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.Interior
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Analysis.Normed.Module.RCLike.Real









set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.SmoothDomain


theorem interior_closure {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M] {Omega : Set M}
    (D : Poincare.Manifold.SmoothDomain (n + 1) Omega) :
    interior (closure Omega) = Omega := by
  let := D.chartedSpace
  exact (Poincare.Manifold.image_interior_of_isSmoothEmbedding
    D.isSmoothEmbedding).symm.trans D.image_interior

end Poincare.Manifold.SmoothDomain

namespace OpenPartialHomeomorph

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [TopologicalSpace M]
  (e : OpenPartialHomeomorph E M) {K : Set M}
  (hs : closedBall (0 : E) 1 ⊆ e.source)
  (himage : e '' closedBall (0 : E) 1 = K)

include hs himage

omit [NormedSpace Real E] in
private theorem isImage_closedBall : e.IsImage (closedBall (0 : E) 1) K := by
  have ht : K ⊆ e.target := by
    rw [← himage]
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hs hx)
  apply IsImage.of_image_eq
  rw [inter_eq_right.mpr hs, inter_eq_right.mpr ht, himage]


theorem image_ball_eq_interior : e '' ball (0 : E) 1 = interior K := by
  have ht : K ⊆ e.target := by
    rw [← himage]
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hs hx)
  have h := (e.isImage_closedBall hs himage).interior.image_eq
  rw [interior_closedBall (0 : E) (by norm_num : (1 : Real) ≠ 0),
    inter_eq_right.mpr (ball_subset_closedBall.trans hs),
    inter_eq_right.mpr (interior_subset.trans ht)] at h
  exact h


theorem image_sphere_eq_frontier [T2Space M] [ProperSpace E] :
    e '' sphere (0 : E) 1 = frontier K := by
  have hclosed : IsClosed K := by
    rw [← himage]
    exact ((isCompact_closedBall 0 1).image_of_continuousOn
      (e.continuousOn.mono hs)).isClosed
  have ht : K ⊆ e.target := by
    rw [← himage]
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hs hx)
  have h := (e.isImage_closedBall hs himage).frontier.image_eq
  rw [frontier_closedBall (0 : E) (by norm_num : (1 : Real) ≠ 0),
    inter_eq_right.mpr (sphere_subset_closedBall.trans hs),
    inter_eq_right.mpr (hclosed.frontier_subset.trans ht)] at h
  exact h

end OpenPartialHomeomorph
