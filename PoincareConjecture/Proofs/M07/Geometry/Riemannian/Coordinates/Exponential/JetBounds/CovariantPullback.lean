import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.AlongCurve.Manifold
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.AlongCurve.Metric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Contraction

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.CoordinateExponential

open PoincareConjecture.ConnectionAlongCurve PoincareConjecture.ConnectionVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem hasDerivAt_metric_inner_along
    (g : RiemannianMetric n M)
    {q : ℝ → M} {V W : (s : ℝ) → TangentSpace (𝓡 n) (q s)} {t : ℝ}
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    (hV : ContDiffAt ℝ ∞ (chartField q (q t) V) t)
    (hW : ContDiffAt ℝ ∞ (chartField q (q t) W) t) :
    HasDerivAt (fun s => g.inner (q s) (V s) (W s))
      (g.inner (q t) (manifoldCovDerivAlong g q V 1 t) (W t) +
        g.inner (q t) (V t) (manifoldCovDerivAlong g q W 1 t)) t := by
  let a : M := q t
  let c := extChartAt (𝓡 n) a
  let B := g.pullbackCoefficients c.symm
  let Q : ℝ → EuclideanSpace ℝ (Fin n) := c ∘ q
  let A : ℝ → EuclideanSpace ℝ (Fin n) := chartField q a V
  let C : ℝ → EuclideanSpace ℝ (Fin n) := chartField q a W
  have ha : q t ∈ c.source := by
    simp [a, c, mem_chart_source]
  have hQ : ContDiffAt ℝ ∞ Q t := by
    dsimp [Q, c]
    exact contDiffAt_chart_curve hq ha
  have hA : ContDiffAt ℝ ∞ A t := by
    simpa only [A, a] using hV
  have hC : ContDiffAt ℝ ∞ C t := by
    simpa only [C, a] using hW
  have hB : ContDiffAt ℝ ∞ B (Q t) := by
    dsimp [B, Q, c]
    exact (g.contDiffOn_chartCoefficients a).contDiffAt
      ((isOpen_extChartAt_target a).mem_nhds
        ((extChartAt (𝓡 n) a).map_source ha))
  have hBinv : (B (Q t)).IsInvertible := by
    dsimp [B, Q, c]
    exact g.isInvertible_chartCoefficients a
      ((extChartAt (𝓡 n) a).map_source ha)
  have hsymm : ∀ᶠ z in 𝓝 (Q t), ∀ u v, B z u v = B z v u := by
    exact Eventually.of_forall (fun _ u v => g.symm _ _ _)
  have hqderiv : HasDerivAt Q (deriv Q t) t :=
    (hQ.differentiableAt (by simp)).hasDerivAt
  have hmetric : HasDerivAt (fun s => B (Q s))
      (fderiv ℝ B (Q t) (deriv Q t)) t := by
    exact (hB.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hqderiv
  have hAd : HasDerivAt A
      (chartField q a (manifoldCovDerivAlong g q V 1) t +
        parallelCoefficient B Q t (A t)) t := by
    dsimp [A, B, Q, c]
    apply hasDerivAt_chartField g hq ha
    simpa only [A] using hA.differentiableAt (by simp)
  have hCd : HasDerivAt C
      (chartField q a (manifoldCovDerivAlong g q W 1) t +
        parallelCoefficient B Q t (C t)) t := by
    dsimp [C, B, Q, c]
    apply hasDerivAt_chartField g hq ha
    simpa only [C] using hC.differentiableAt (by simp)
  have hpair := (hmetric.clm_apply hAd).clm_apply hCd
  have hcoef (u v : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ B (Q t) (deriv Q t) u v =
        B (Q t) (coordinateChristoffel B (Q t) (deriv Q t) u) v +
          B (Q t) u (coordinateChristoffel B (Q t) (deriv Q t) v) := by
    exact fderiv_metric_eq_christoffel (hB.differentiableAt (by simp)) hBinv hsymm
      u v (deriv Q t)
  have hderiv_coord :
      ((((fderiv ℝ B (Q t)) (deriv Q t)) (A t) +
          (B (Q t)) (chartField q a (manifoldCovDerivAlong g q V 1) t +
            (parallelCoefficient B Q t) (A t))) (C t) +
        ((B (Q t)) (A t))
          (chartField q a (manifoldCovDerivAlong g q W 1) t +
            (parallelCoefficient B Q t) (C t))) =
      (B (Q t)) (chartField q a (manifoldCovDerivAlong g q V 1) t) (C t) +
        (B (Q t)) (A t)
          (chartField q a (manifoldCovDerivAlong g q W 1) t) := by
    simp only [parallelCoefficient, christoffelBilinear_apply, neg_apply,
      add_apply, map_add, map_neg]
    rw [hcoef]
    ring
  have hpair'' := hpair.congr_deriv hderiv_coord
  have hVinner :
      (B (Q t)) (chartField q a (manifoldCovDerivAlong g q V 1) t) (C t) =
        g.inner (q t) (manifoldCovDerivAlong g q V 1 t) (W t) := by
    change g.pullbackCoefficients c.symm (c (q t))
      (chartField q a (manifoldCovDerivAlong g q V 1) t)
      (chartField q a W t) = _
    exact chartField_inner g (manifoldCovDerivAlong g q V 1) W ha
  have hWinner :
      (B (Q t)) (A t) (chartField q a (manifoldCovDerivAlong g q W 1) t) =
        g.inner (q t) (V t) (manifoldCovDerivAlong g q W 1 t) := by
    change g.pullbackCoefficients c.symm (c (q t))
      (chartField q a V t)
      (chartField q a (manifoldCovDerivAlong g q W 1) t) = _
    exact chartField_inner g V (manifoldCovDerivAlong g q W 1) ha
  have hpair_eq := hpair''.congr_of_eventuallyEq (show
      (fun s => g.inner (q s) (V s) (W s)) =ᶠ[𝓝 t]
        (fun s => B (Q s) (A s) (C s)) from ?_)
  · apply hpair_eq.congr_deriv
    rw [hVinner, hWinner]
  · have hnear := hq.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source a).mem_nhds ha)
    filter_upwards [hnear] with s hs
    exact (chartField_inner g V W hs).symm

theorem covariantTensorDerivative_metric_pullback_zero
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (x : M) (v a b : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y w => g.inner y (w 0) (w 1))
      x ![v, a, b] = 0 := by
  exact D.covariantTensorDerivative_metric_eq_zero x v a b

end PoincareConjecture.CoordinateExponential
