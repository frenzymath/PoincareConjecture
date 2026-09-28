import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.CompactImageRegularity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.PullbackGeodesics

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.M28

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {N : Type*} [TopologicalSpace N] [T2Space N]
  [ChartedSpace E N] [IsManifold (𝓡 3) ∞ N]

theorem mem_intrinsicImage_regularPoints_of_euclidean_buffer
    (h : RiemannianMetric 3 N) (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E N ∞)
    {a : ℝ} (ha : 0 < a) (hsource : ball (0 : E) a ⊆ e.source)
    (hlower : ∀ z ∈ ball (0 : E) a, ∀ v : E,
      (1 / 8 : ℝ) * ‖v‖ ^ 2 ≤ h.inner (e z)
        (mfderiv (𝓡 3) (𝓡 3) e z v) (mfderiv (𝓡 3) (𝓡 3) e z v))
    {x : E} (hx : x ∈ closedBall (0 : E) (a / 64)) :
    let V : TopologicalSpace.Opens E := ⟨ball 0 a, isOpen_ball⟩
    let W : TopologicalSpace.Opens N :=
      ⟨e '' (V : Set E), e.toOpenPartialHomeomorph.isOpen_image_of_subset_source
        V.isOpen hsource⟩
    ∀ p : W, (p : N) = e x →
      p ∈ regularPoints (intrinsicOpenMetric h W) (a / 8) := by
  let V : TopologicalSpace.Opens E := ⟨ball 0 a, isOpen_ball⟩
  let W : TopologicalSpace.Opens N :=
    ⟨e '' (V : Set E), e.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      V.isOpen hsource⟩
  have hxV : x ∈ (V : Set E) := closedBall_subset_ball (by linarith) hx
  have hKV : closedBall (0 : E) (a / 2) ⊆ (V : Set E) :=
    closedBall_subset_ball (by linarith)
  have hbound : ∀ z ∈ (V : Set E), ∀ v : TangentSpace (𝓡 3) z,
      (RiemannianMetric.euclideanMetric 3).inner z v v ≤ (3 : ℝ) ^ 2 *
        h.inner (e z) (mfderiv (𝓡 3) (𝓡 3) e z v)
          (mfderiv (𝓡 3) (𝓡 3) e z v) := by
    intro z hz v
    rw [RiemannianMetric.euclideanMetric_inner, real_inner_self_eq_norm_sq]
    nlinarith [hlower z hz v, sq_nonneg ‖(v : E)‖]
  have hball : (RiemannianMetric.euclideanMetric 3).ball x (3 * (a / 8)) ⊆
      closedBall (0 : E) (a / 2) := by
    intro y hy
    change (RiemannianMetric.euclideanMetric 3).edist x y <
      ENNReal.ofReal (3 * (a / 8)) at hy
    rw [RiemannianMetric.euclideanMetric_edist, edist_dist] at hy
    have hxy : dist x y < 3 * (a / 8) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hy
    have hx0 : dist x 0 ≤ a / 64 := hx
    have hy0 := dist_triangle y x (0 : E)
    rw [dist_comm y x] at hy0
    change dist y 0 ≤ a / 2
    linarith
  change ∀ p : W, (p : N) = e x →
    p ∈ regularPoints (intrinsicOpenMetric h W) (a / 8)
  intro p hp
  have heq : (⟨e x, x, hxV, rfl⟩ : W) = p := Subtype.ext hp.symm
  rw [← heq]
  exact mem_intrinsicImage_regularPoints_of_compact_inverse_buffer
    (RiemannianMetric.euclideanMetric 3) h e V hsource
    (isCompact_closedBall 0 (a / 2)) hKV (by norm_num : (0 : ℝ) < 3)
    hbound hxV (by positivity) hball

end PoincareConjecture.M28
