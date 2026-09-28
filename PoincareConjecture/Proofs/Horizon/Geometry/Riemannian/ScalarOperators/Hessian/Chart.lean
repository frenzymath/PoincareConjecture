import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalExtension








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem hessian_in_locally_invertible_coordinates (D : LeviCivitaData g)
    {e : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U)
    (he : ∀ y ∈ U, ContMDiffAt (𝓡 n) (𝓡 n) ∞ e y)
    (hi : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) {f : M → ℝ}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (e x))
    (v w : EuclideanSpace ℝ (Fin n)) :
    D.hessian f (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x w) =
      fderiv ℝ (fderiv ℝ (f ∘ e)) x v w -
        fderiv ℝ (f ∘ e) x
          (CoordinateExponential.christoffelBilinear (g.pullbackCoefficients e) x v w) := by
  obtain ⟨gE, DE, V, hVo, hxV, _, hE⟩ :=
    RiemannianMetric.exists_local_realization hU hx
      (g.pullbackCoefficients e)
      (fun y hy => (g.contDiffAt_pullbackCoefficients (he y hy)).contDiffWithinAt)
      (fun y _ b d => g.symm _ _ _)
      (fun y hy b hb => by
        apply g.pos (e y)
        intro hzero
        apply hb
        apply (hi y hy).injective
        rw [map_zero]
        exact hzero)
  have heq : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients e := by
    filter_upwards [hVo.mem_nhds hxV] with y hy
    exact hE y hy
  have hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible :=
    (hU.eventually_mem hx).mono fun y hy => hi y hy
  have hmetric : ∀ᶠ y in 𝓝 x, ∀ b d : EuclideanSpace ℝ (Fin n),
      gE.inner y b d = g.inner (e y)
        (mfderiv (𝓡 n) (𝓡 n) e y b) (mfderiv (𝓡 n) (𝓡 n) e y d) := by
    filter_upwards [heq] with y hy b d
    exact congrArg (fun B => B b d) hy
  have hΓ : CoordinateExponential.christoffelBilinear gE.euclideanCoefficients x =
      CoordinateExponential.christoffelBilinear (g.pullbackCoefficients e) x := by
    simp only [CoordinateExponential.christoffelBilinear, heq.self_of_nhds, heq.fderiv_eq]
  rw [← DE.hessian_comp_of_metric_pullback D (he x hx) hinv hmetric hf,
    DE.hessian_eq_fderiv_sub_christoffel
      (contMDiffAt_iff_contDiffAt.mp (hf.comp x (he x hx))), hΓ]



theorem hessian_in_chart (D : LeviCivitaData g) {f : M → ℝ} (a : M)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ (extChartAt (𝓡 n) a).target)
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ((extChartAt (𝓡 n) a).symm x))
    (v w : EuclideanSpace ℝ (Fin n)) :
    D.hessian f ((extChartAt (𝓡 n) a).symm x)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm x v)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm x w) =
      fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (𝓡 n) a).symm)) x v w -
        fderiv ℝ (f ∘ (extChartAt (𝓡 n) a).symm) x
          (CoordinateExponential.christoffelBilinear
            (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm) x v w) := by
  let c := extChartAt (𝓡 n) a
  have hc (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) a hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  have hi (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  exact D.hessian_in_locally_invertible_coordinates (isOpen_extChartAt_target a) hc hi hx hf v w

end PoincareConjecture.LeviCivitaData
