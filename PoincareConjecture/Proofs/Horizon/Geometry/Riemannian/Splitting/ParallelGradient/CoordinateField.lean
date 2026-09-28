import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Euclidean
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.AlongCurve.Metric







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem contDiffAt_mpullback_gradient
    {D : LeviCivitaData g} {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (a : M)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ (extChartAt (𝓡 n) a).target) :
    ContDiffAt ℝ ∞
      (mpullback (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm (D.gradient f)) x := by
  have hc := (contMDiffWithinAt_extChartAt_symm_target (I := 𝓡 n) (n := ∞) a hx).contMDiffAt
    (extChartAt_target_mem_nhds' hx)
  have hi : (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm x).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hx
  have hG := (D.contMDiffAt_gradient (hf ((extChartAt (𝓡 n) a).symm x))).mpullback_vectorField_preimage
    hc hi (by simp)
  rw [Bundle.contMDiffAt_totalSpace] at hG
  apply contMDiffAt_iff_contDiffAt.mp
  simpa using hG.2


theorem fderiv_mpullback_gradient_eq_neg_christoffel
    {D : LeviCivitaData g} {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hzero : HasZeroHessian D f)
    (a : M) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ (extChartAt (𝓡 n) a).target) (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (mpullback (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm (D.gradient f)) x v =
      -coordinateChristoffel (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm) x v
        (mpullback (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm (D.gradient f) x) := by
  let c := extChartAt (𝓡 n) a
  let G := mpullback (𝓡 n) (𝓡 n) c.symm (D.gradient f)
  have hc (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) a hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  have hi (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  obtain ⟨gE, DE, V, hVo, hxV, _, hE⟩ :=
    exists_local_realization (isOpen_extChartAt_target a) hx
      (g.pullbackCoefficients c.symm) (g.contDiffOn_chartCoefficients a)
      (fun y _ b d => g.symm _ _ _)
      (fun y hy b hb => by
        apply g.pos (c.symm y)
        intro hzero
        apply hb
        apply (hi y hy).injective
        rw [map_zero]
        exact hzero)
  have heq : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients c.symm := by
    filter_upwards [hVo.mem_nhds hxV] with y hy
    exact hE y hy
  have hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible :=
    Filter.mem_of_superset (extChartAt_target_mem_nhds' hx) hi
  have hmetric : ∀ᶠ y in 𝓝 x, ∀ b d : EuclideanSpace ℝ (Fin n),
      gE.inner y b d = g.inner (c.symm y)
        (mfderiv (𝓡 n) (𝓡 n) c.symm y b)
        (mfderiv (𝓡 n) (𝓡 n) c.symm y d) := by
    filter_upwards [heq] with y hy b d
    exact congrArg (fun B => B b d) hy
  have hG : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% G) x :=
    (D.contMDiffAt_gradient (hf (c.symm x))).mpullback_vectorField_preimage
      (hc x hx) (hi x hx) (by simp)
  have hGd : DifferentiableAt ℝ G x := by
    rw [Bundle.contMDiffAt_totalSpace] at hG
    have hG' : ContMDiffAt (𝓡 n) (𝓡 n) ∞ G x := by simpa using hG.2
    exact (contMDiffAt_iff_contDiffAt.mp hG').differentiableAt (by simp)
  have hconn := DE.connection_mpullback_of_metric_pullback D (hc x hx) hinv hmetric
    ((D.contMDiffAt_gradient (hf (c.symm x))).mdifferentiableAt (by simp)) v
  rw [connection_gradient_eq_zero_of_hasZeroHessian hf hzero, map_zero] at hconn
  change DE.connection G x v = 0 at hconn
  rw [DE.connection_eq_fderiv_add hGd] at hconn
  unfold LeviCivitaData.euclideanConnection at hconn
  rw [DE.connection_const_eq_inverse] at hconn
  change fderiv ℝ G x v + coordinateChristoffel gE.euclideanCoefficients x v (G x) = 0 at hconn
  simp only [coordinateChristoffel, heq.self_of_nhds, heq.fderiv_eq] at hconn
  exact eq_neg_of_add_eq_zero_left hconn



theorem mpullback_gradient_eq_chart_gradient
    {D : LeviCivitaData g} {f : M → ℝ} (a : M)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ (extChartAt (𝓡 n) a).target) :
    mpullback (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm (D.gradient f) x =
      mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) ((extChartAt (𝓡 n) a).symm x)
        (D.gradient f ((extChartAt (𝓡 n) a).symm x)) := by
  let c := extChartAt (𝓡 n) a
  have hi : (mfderiv (𝓡 n) (𝓡 n) c.symm x).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hx
  have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    (I := 𝓡 n) (c.map_target hx)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hcomp
  change (mfderiv (𝓡 n) (𝓡 n) c.symm (c (c.symm x))).comp
    (mfderiv (𝓡 n) (𝓡 n) c (c.symm x)) = ContinuousLinearMap.id ℝ _ at hcomp
  rw [c.right_inv hx] at hcomp
  apply hi.injective
  rw [mpullback, hi.self_apply_inverse]
  have h := congrArg (fun L => L (D.gradient f (c.symm x))) hcomp
  change mfderiv (𝓡 n) (𝓡 n) c.symm x
    (mfderiv (𝓡 n) (𝓡 n) c (c.symm x) (D.gradient f (c.symm x))) =
      D.gradient f (c.symm x) at h
  exact h.symm



theorem coordinate_gradient_metric_derivative_eq_zero
    {D : LeviCivitaData g} {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hzero : HasZeroHessian D f)
    (a : M) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ (extChartAt (𝓡 n) a).target) (v w : EuclideanSpace ℝ (Fin n)) :
    let B := g.pullbackCoefficients (extChartAt (𝓡 n) a).symm
    let G := mpullback (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm (D.gradient f)
    fderiv ℝ B x (G x) v w + B x (fderiv ℝ G x v) w + B x v (fderiv ℝ G x w) = 0 := by
  let B := g.pullbackCoefficients (extChartAt (𝓡 n) a).symm
  let G := mpullback (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm (D.gradient f)
  have hBd : DifferentiableAt ℝ B x :=
    ((g.contDiffOn_chartCoefficients a).contDiffAt
      (extChartAt_target_mem_nhds' hx)).differentiableAt (by simp)
  have hBsymm : ∀ᶠ y in 𝓝 x, ∀ v w, B y v w = B y w v :=
    Filter.Eventually.of_forall (fun y v w => g.symm _ _ _)
  have hsymm (u v : EuclideanSpace ℝ (Fin n)) :
      coordinateChristoffel B x u v = coordinateChristoffel B x v u :=
    CoordinateExponential.christoffelBilinear_symm hBd hBsymm u v
  change fderiv ℝ B x (G x) v w + B x (fderiv ℝ G x v) w +
    B x v (fderiv ℝ G x w) = 0
  rw [fderiv_mpullback_gradient_eq_neg_christoffel hf hzero a hx v,
    fderiv_mpullback_gradient_eq_neg_christoffel hf hzero a hx w,
    CoordinateExponential.fderiv_metric_eq_christoffel hBd
      (g.isInvertible_chartCoefficients a hx) hBsymm]
  rw [hsymm v, hsymm w]
  simp only [map_neg, neg_apply]
  ring

end PoincareConjecture.RiemannianMetric
