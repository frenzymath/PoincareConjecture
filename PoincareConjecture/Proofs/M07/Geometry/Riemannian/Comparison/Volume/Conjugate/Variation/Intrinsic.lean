import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Piece
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.AlongCurve.Manifold








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.ConjugateVariation

open CoordinateExponential ConnectionVariation ConnectionAlongCurve

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


def intrinsicIndexIntegrand (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (q : ℝ → M) (V : (t : ℝ) → TangentSpace (𝓡 n) (q t)) (t : ℝ) : ℝ :=
  g.inner (q t) (manifoldCovDerivAlong g q V 1 t) (manifoldCovDerivAlong g q V 1 t) -
    g.inner (q t) (D.curvature (q t) (V t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) (V t)


theorem chartCoefficients_apply (g : RiemannianMetric n M) (a : M) {z : M}
    (hz : z ∈ (extChartAt (𝓡 n) a).source) (v w : TangentSpace (𝓡 n) z) :
    g.pullbackCoefficients (extChartAt (𝓡 n) a).symm (extChartAt (𝓡 n) a z)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) z v)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) z w) = g.inner z v w := by
  let c := extChartAt (𝓡 n) a
  have hid := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := 𝓡 n) hz
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hid
  have hv (b : TangentSpace (𝓡 n) z) :
      mfderiv (𝓡 n) (𝓡 n) c.symm (c z) (mfderiv (𝓡 n) (𝓡 n) c z b) = b :=
    congrArg (fun L => L b) hid
  change g.inner (c.symm (c z))
    (mfderiv (𝓡 n) (𝓡 n) c.symm (c z) (mfderiv (𝓡 n) (𝓡 n) c z v))
    (mfderiv (𝓡 n) (𝓡 n) c.symm (c z) (mfderiv (𝓡 n) (𝓡 n) c z w)) = _
  rw [hv, hv, c.left_inv hz]



theorem isMetricCompatibleAt_chartCoefficients (g : RiemannianMetric n M) (a : M)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ (extChartAt (𝓡 n) a).target) :
    IsMetricCompatibleAt (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
      (christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)) x := by
  intro X V W
  exact fderiv_metric_eq_christoffel
    (((g.contDiffOn_chartCoefficients a).contDiffAt
      ((isOpen_extChartAt_target a).mem_nhds hx)).differentiableAt (by simp))
    (g.isInvertible_chartCoefficients a hx)
    (Eventually.of_forall fun _ _ _ => g.symm _ _ _) V W X


theorem christoffelBilinear_chart_symm (g : RiemannianMetric n M) (a : M)
    (x v w : EuclideanSpace ℝ (Fin n)) :
    christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm) x v w =
      christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm) x w v := by
  by_cases hB : DifferentiableAt ℝ
      (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm) x
  · exact christoffelBilinear_symm hB
      (Eventually.of_forall fun _ _ _ => g.symm _ _ _) v w
  · simp only [christoffelBilinear_apply, coordinateChristoffel,
      fderiv_zero_of_not_differentiableAt hB, metricKoszulCovector]
    simp



theorem energyDensity_eq_half_tangentNorm_sq
    (g : RiemannianMetric n M) (a : M)
    {q : ℝ → M} {u : ℝ × ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hq : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) q t)
    (ha : q t ∈ (extChartAt (𝓡 n) a).source)
    (hu : DifferentiableAt ℝ u (0, t))
    (hbase : (fun s => u (0, s)) =ᶠ[𝓝 t] (extChartAt (𝓡 n) a) ∘ q) :
    energyDensity (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm) u (0, 1) (0, t) =
      (1 / 2 : ℝ) * (g.tangentNorm (q t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) ^ 2 := by
  have hpoint : u (0, t) = extChartAt (𝓡 n) a (q t) := hbase.self_of_nhds
  have hd := mfderiv_comp t (mdifferentiableAt_extChartAt
    (by simpa only [extChartAt_source] using ha)) hq
  rw [mfderiv_eq_fderiv] at hd
  have hdu := hu.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t (0 : ℝ)).prodMk (hasDerivAt_id t))
  have hvel : fderiv ℝ u (0, t) (0, 1) =
      mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) (q t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) := by
    exact hdu.deriv.symm.trans (hbase.deriv_eq.trans (congrArg (fun L => L 1) hd))
  rw [energyDensity, hvel, hpoint, chartCoefficients_apply g a ha]
  congr 1
  symm
  apply Real.sq_sqrt
  by_cases hzero : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1 = 0
  · simp [hzero]
  · exact (g.pos _ _ hzero).le



theorem chartIndexIntegrand_eq_intrinsic
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (a : M)
    {q : ℝ → M} {V : (t : ℝ) → TangentSpace (𝓡 n) (q t)}
    {u : ℝ × ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    (ha : q t ∈ (extChartAt (𝓡 n) a).source)
    (hV : DifferentiableAt ℝ (chartField q a V) t)
    (hu : ContDiffAt ℝ 2 u (0, t))
    (hbase : (fun s => u (0, s)) =ᶠ[𝓝 t] (extChartAt (𝓡 n) a) ∘ q)
    (hfield : (fun s => fderiv ℝ u (0, s) (1, 0)) =ᶠ[𝓝 t] chartField q a V) :
    chartIndexIntegrand (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
      (christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)) u t =
      intrinsicIndexIntegrand g D q V t := by
  let c := extChartAt (𝓡 n) a
  let B := g.pullbackCoefficients c.symm
  let A := christoffelBilinear B
  let Y := fun p : ℝ × ℝ => fderiv ℝ u p (1, 0)
  let T := mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓡 n) (𝓡 n) c (q t)
  have hpoint : u (0, t) = c (q t) := hbase.self_of_nhds
  have hYpoint : Y (0, t) = L (V t) := hfield.self_of_nhds
  have hcu := contDiffAt_chart_curve hq ha
  have hline : HasDerivAt (fun s : ℝ => ((0 : ℝ), s)) (0, 1) t :=
    (hasDerivAt_const t (0 : ℝ)).prodMk (hasDerivAt_id t)
  have hvel : fderiv ℝ u (0, t) (0, 1) = L T := by
    have hdu := (hu.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t hline
    have hdc := mfderiv_comp t (mdifferentiableAt_extChartAt
      (by simpa only [extChartAt_source] using ha)) (hq.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hdc
    have hdc1 : deriv (c ∘ q) t = L T := congrArg (fun f => f 1) hdc
    rw [← hdc1, ← hbase.deriv_eq]
    exact hdu.deriv.symm
  have hY1 : ContDiffAt ℝ 1 Y (0, t) :=
    (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hY : DifferentiableAt ℝ Y (0, t) := hY1.differentiableAt (by norm_num)
  have hcov : covDerivAlong A u Y (0, 1) (0, t) =
      L (manifoldCovDerivAlong g q V 1 t) := by
    rw [← covDerivAlong_comp_curve A (hu.differentiableAt (by norm_num)) hY hline]
    change covDerivAlong A (fun s => u (0, s))
      (fun s => fderiv ℝ u (0, s) (1, 0)) 1 t = _
    rw [covDerivAlong_congr_base A _ hbase,
      covDerivAlong_congr A _ hfield]
    exact (manifoldCovDerivAlong_in_chart g a ha hq.continuousAt
      (hcu.differentiableAt (by simp)) hV 1).symm
  have hB := (g.contDiffOn_chartCoefficients a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds (c.map_source ha))
  have hA : DifferentiableAt ℝ A (c (q t)) :=
    (contDiffAt_christoffelBilinear hB (g.isInvertible_chartCoefficients a
      (c.map_source ha))).differentiableAt (by simp)
  have hR : coordinateCurvature B (c (q t)) (L (V t)) (L T) (L T) =
      L (D.curvature (q t) (V t) T T) :=
    coordinateCurvature_in_chart g D a ha (V t) T T
  have hmetric (v w : TangentSpace (𝓡 n) (q t)) :
      B (c (q t)) (L v) (L w) = g.inner (q t) v w :=
    chartCoefficients_apply g a ha v w
  change B (u (0, t)) (covDerivAlong A u Y (0, 1) (0, t))
    (covDerivAlong A u Y (0, 1) (0, t)) -
    B (u (0, t)) (christoffelCurvature A (u (0, t)) (Y (0, t))
      (fderiv ℝ u (0, t) (0, 1)) (fderiv ℝ u (0, t) (0, 1))) (Y (0, t)) = _
  rw [hcov, hpoint, hYpoint, hvel,
    ← coordinateCurvature_eq_christoffelCurvature hA, hR, hmetric, hmetric]
  rfl

end PoincareConjecture.ConjugateVariation
