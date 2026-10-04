import PoincareLib.Geometry.Riemannian.Metric
import PoincareLib.Geometry.Manifold.InverseFunction.SmoothInverse

/-!
# Metric-preserving coordinate transitions

Positive definiteness makes the derivative of a metric-preserving map
injective. Equal dimensions give invertibility, so an injective smooth such
map is a diffeomorphism onto an open subset.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Topology

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]

/-- A tangent map preserving positive metrics between equal-dimensional
manifolds is invertible. -/
theorem mfderiv_bijective_of_pullback_eq (g : RiemannianMetric n M)
    (h : RiemannianMetric n N) {f : M → N} (x : M)
    (hmetric : ∀ v w : TangentSpace (𝓡 n) x,
      h.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x v)
        (mfderiv (𝓡 n) (𝓡 n) f x w) = g.inner x v w) :
    Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x) := by
  let L := mfderiv (𝓡 n) (𝓡 n) f x
  have hi : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro v hv
    by_contra hne
    have hpos := g.pos x v hne
    have heq := hmetric v v
    change h.inner (f x) (L v) (L v) = g.inner x v v at heq
    rw [hv] at heq
    simp at heq
    exact (ne_of_gt hpos) heq.symm
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
    unfold TangentSpace
    infer_instance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (f x)) := by
    unfold TangentSpace
    infer_instance
  have hfin : Module.finrank ℝ (TangentSpace (𝓡 n) x) =
      Module.finrank ℝ (TangentSpace (𝓡 n) (f x)) := by
    unfold TangentSpace
    rfl
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hi⟩

/-- An injective smooth metric-preserving map is an open embedding. -/
theorem isOpenEmbedding_of_injective_pullback_eq (g : RiemannianMetric n M)
    (h : RiemannianMetric n N) {f : M → N}
    (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f) (hinj : Function.Injective f)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 n) x),
      h.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x v)
        (mfderiv (𝓡 n) (𝓡 n) f x w) = g.inner x v w) :
    IsOpenEmbedding f := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap hf.continuous hinj
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨x, hx, rfl⟩
  rw [← Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective (hf x)
    (g.mfderiv_bijective_of_pullback_eq h x (hmetric x))]
  exact image_mem_map (hU.mem_nhds hx)

/-- The inverse of an injective smooth metric-preserving map is smooth on
its image. -/
theorem contMDiffOn_invFun_of_injective_pullback_eq [Nonempty M] (g : RiemannianMetric n M)
    (h : RiemannianMetric n N) {f : M → N}
    (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f) (hinj : Function.Injective f)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 n) x),
      h.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x v)
        (mfderiv (𝓡 n) (𝓡 n) f x w) = g.inner x v w) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (Function.invFun f) (range f) := by
  rintro _ ⟨x, rfl⟩
  apply ContMDiffAt.contMDiffWithinAt
  exact Poincare.contMDiffAt_of_local_left_inverse (hf x)
    (g.mfderiv_bijective_of_pullback_eq h x (hmetric x))
    (Eventually.of_forall (Function.leftInverse_invFun hinj))

end PoincareMT.RiemannianMetric
