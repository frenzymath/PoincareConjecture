import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Laplacian.Harmonic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalExtension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle InnerProductSpace

namespace PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def chartMetric (g : RiemannianMetric n M) (p : M) :=
  g.pullbackCoefficients (extChartAt (𝓡 n) p).symm

def chartDrift (g : RiemannianMetric n M) (p : M)
    (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ∑ i, CoordinateExponential.christoffelBilinear (chartMetric g p) y
    (EuclideanSpace.basisFun (Fin n) ℝ i)
    ((chartMetric g p y).inverse (EuclideanSpace.proj i))

def chartOperator (g : RiemannianMetric n M) (p : M)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (∑ i, fderiv ℝ (fderiv ℝ f) y (EuclideanSpace.basisFun (Fin n) ℝ i)
    ((chartMetric g p y).inverse (EuclideanSpace.proj i))) -
      fderiv ℝ f y (chartDrift g p y)

theorem laplacian_in_chart {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {f : M → ℝ} (p : M) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (extChartAt (𝓡 n) p).target)
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ((extChartAt (𝓡 n) p).symm y)) :
    D.laplacian f ((extChartAt (𝓡 n) p).symm y) =
      chartOperator g p (f ∘ (extChartAt (𝓡 n) p).symm) y := by
  let c := extChartAt (𝓡 n) p
  have hc (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm x :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) p hx).contMDiffAt
      (extChartAt_target_mem_nhds' hx)
  have hi (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ c.target) :
      (mfderiv (𝓡 n) (𝓡 n) c.symm x).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hx
  obtain ⟨gE, DE, V, hVo, hyV, _, hE⟩ :=
    RiemannianMetric.exists_local_realization (isOpen_extChartAt_target p) hy
      (g.pullbackCoefficients c.symm) (g.contDiffOn_chartCoefficients p)
      (fun x _ v w => g.symm _ _ _)
      (fun x hx v hv => by
        apply g.pos (c.symm x)
        intro hz
        apply hv
        apply (hi x hx).injective
        rw [map_zero]
        exact hz)
  have heq : gE.euclideanCoefficients =ᶠ[𝓝 y] chartMetric g p := by
    filter_upwards [hVo.mem_nhds hyV] with x hx
    exact hE x hx
  have hinv : ∀ᶠ x in 𝓝 y, (mfderiv (𝓡 n) (𝓡 n) c.symm x).IsInvertible :=
    Filter.mem_of_superset (extChartAt_target_mem_nhds' hy) hi
  have hmetric : ∀ᶠ x in 𝓝 y, ∀ v w : EuclideanSpace ℝ (Fin n),
      gE.inner x v w = g.inner (c.symm x)
        (mfderiv (𝓡 n) (𝓡 n) c.symm x v)
        (mfderiv (𝓡 n) (𝓡 n) c.symm x w) := by
    filter_upwards [heq] with x hx v w
    exact congrArg (fun B => B v w) hx
  have hΓ : CoordinateExponential.christoffelBilinear gE.euclideanCoefficients y =
      CoordinateExponential.christoffelBilinear (chartMetric g p) y := by
    simp only [CoordinateExponential.christoffelBilinear, heq.self_of_nhds, heq.fderiv_eq]
  rw [← DE.laplacian_comp_of_metric_pullback D (hc y hy) hinv hmetric hf,
    DE.laplacian_eq_sum_fderiv_sub_christoffel
      (contMDiffAt_iff_contDiffAt.mp (hf.comp y (hc y hy))), hΓ]
  change (∑ i, fderiv ℝ (fderiv ℝ (f ∘ c.symm)) y
    (EuclideanSpace.basisFun (Fin n) ℝ i)
    ((gE.euclideanCoefficients y).inverse (EuclideanSpace.proj i))) -
      fderiv ℝ (f ∘ c.symm) y (∑ i,
        CoordinateExponential.christoffelBilinear (chartMetric g p) y
          (EuclideanSpace.basisFun (Fin n) ℝ i)
          ((gE.euclideanCoefficients y).inverse (EuclideanSpace.proj i))) = _
  rw [heq.self_of_nhds]
  rfl

theorem chartOperator_congr (g : RiemannianMetric n M) (p : M)
    {f h : EuclideanSpace ℝ (Fin n) → ℝ} {y : EuclideanSpace ℝ (Fin n)}
    (he : f =ᶠ[𝓝 y] h) : chartOperator g p f y = chartOperator g p h y := by
  unfold chartOperator
  rw [he.fderiv_eq, he.fderiv.fderiv_eq]

end PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple
