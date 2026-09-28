import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem m65Exists_chartMetric (g : RiemannianMetric n M) (p : M) :
    ∃ (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (_D : LeviCivitaData gE),
      ∀ᶠ y in 𝓝 (extChartAt (𝓡 n) p p), ∀ u v : EuclideanSpace ℝ (Fin n),
        gE.inner y u v = g.inner ((extChartAt (𝓡 n) p).symm y)
          (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p).symm y u)
          (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p).symm y v) := by
  let c := extChartAt (𝓡 n) p
  have hc (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) p hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  have hi (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  obtain ⟨gE, DE, V, hVo, hpV, _, heq⟩ :=
    RiemannianMetric.exists_local_realization (isOpen_extChartAt_target p)
      (mem_extChartAt_target p) (g.pullbackCoefficients c.symm)
      (fun y hy => (g.contDiffAt_pullbackCoefficients (hc y hy)).contDiffWithinAt)
      (fun y _ u v => g.symm (c.symm y) _ _)
      (fun y hy v hv => by
        apply g.pos (c.symm y)
        intro hzero
        apply hv
        apply (hi y hy).injective
        rw [map_zero]
        convert! hzero using 1)
  refine ⟨gE, DE, ?_⟩
  filter_upwards [hVo.mem_nhds hpV] with y hy u v
  exact congrArg (fun B => B u v) (heq y hy)

end PoincareConjecture
