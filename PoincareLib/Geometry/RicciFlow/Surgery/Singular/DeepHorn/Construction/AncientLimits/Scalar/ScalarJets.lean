import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.SourceNames
import PoincareLib.Geometry.Riemannian.Homothety.Curvature.Contractions
import PoincareLib.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.Operator
import Mathlib.Analysis.InnerProductSpace.Trace
open scoped PoincareMT.DeepHornSource

/-!
# The actual scalar trace on metric two-jets

Morgan--Tian equation (3.7), printed p. 41, and Claim 11.35, pp. 289-291.
The scalar trace is a smooth function of the actual metric two-jet on
the invertible domain. Differentiating this identity twice will recover
the actual Laplacian needed for the signed neck estimate.

Locally re-derived from M44 Sec16_1_CapPersistence/Lemma11_2_ScalarJet:
`metricTrace_eq_inverse_contraction`, `jetScalarCurvature`,
`contDiffAt_jetScalarCurvature`, and `jetScalarCurvature_metricTwoJet`.
No later proof is imported. The bounded derivation is
`claim11_35-scalar-laplacian-jets.md`.
-/

set_option autoImplicit false
-- Native two-jet slots identify the Euclidean and manifold tangent instances.
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareMT.M32

open PoincareMT.SpacetimeBounds

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

/-- The actual metric trace in fixed Euclidean coordinates, including
dimension zero; equation (3.7), p. 41, in Claim 11.35, p. 289. -/
theorem metricTrace_eq_inverse_contraction {n : ℕ}
    (g : RiemannianMetric n (E n)) (x : E n)
    (B : E n →ₗ[ℝ] E n →ₗ[ℝ] ℝ) :
    (∑ k, B (g.orthonormalBasis x k) (g.orthonormalBasis x k)) =
      ∑ i, ∑ j, g.inverseCoefficients x i j *
        B (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  let C := B.toContinuousBilinearMap
  let T : E n →L[ℝ] E n := (g.euclideanCoefficients x).inverse.comp C
  have htrace : LinearMap.trace ℝ (E n) T.toLinearMap =
      ∑ k, B (g.orthonormalBasis x k) (g.orthonormalBasis x k) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : E n → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have ht := LinearMap.trace_eq_sum_inner
      (show TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x from T.toLinearMap)
      (g.orthonormalBasis x)
    refine ht.trans ?_
    apply Finset.sum_congr rfl
    intro i _
    change g.inner x (g.orthonormalBasis x i)
      ((g.inner x).inverse (C (g.orthonormalBasis x i))) = _
    rw [g.symm, (g.inner_isInvertible x).self_apply_inverse]
    rfl
  rw [← htrace, LinearMap.trace_eq_matrix_trace ℝ
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  apply Finset.sum_congr rfl
  intro i _
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hdual : EuclideanSpace.proj i (T (e i)) =
      B (e i) ((g.inner x).inverse (EuclideanSpace.proj i)) := by
    calc
      _ = g.inner x ((g.inner x).inverse (EuclideanSpace.proj i)) (T (e i)) := by
        rw [(g.inner_isInvertible x).self_apply_inverse]
        rfl
      _ = g.inner x (T (e i)) ((g.inner x).inverse (EuclideanSpace.proj i)) := g.symm x _ _
      _ = _ := by
        change g.inner x ((g.inner x).inverse (C (e i)))
          ((g.inner x).inverse (EuclideanSpace.proj i)) = _
        rw [(g.inner_isInvertible x).self_apply_inverse]
        rfl
  have hexp := congrArg (B (e i))
    (e.toBasis.sum_repr ((g.inner x).inverse (EuclideanSpace.proj i)))
  simpa only [e, map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    RiemannianMetric.inverseCoefficients, PiLp.proj_apply,
    ContinuousLinearMap.coe_coe] using hdual.trans hexp.symm

/-- The inverse-metric trace of the native Ricci two-jet, as used in
the scalar evolution identity (equation (3.7), p. 41). -/
noncomputable def scalarMetricTraceTwoJet {n : ℕ} (J : MetricTwoJet n) : ℝ :=
  ∑ i, ∑ j, EuclideanSpace.proj j (J.1.inverse (EuclideanSpace.proj i)) *
    jetRicci J (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)

/-- The scalar trace is smooth on invertible two-jets; the four-jet
calculation in Claim 11.35, printed p. 289, differentiates this function. -/
theorem contDiffAt_scalarMetricTraceTwoJet {n : ℕ} {J : MetricTwoJet n}
    (hJ : J.1.IsInvertible) : ContDiffAt ℝ ∞ (@scalarMetricTraceTwoJet n) J := by
  have hI : ContDiffAt ℝ ∞ (fun K : MetricTwoJet n => K.1.inverse) J :=
    hJ.contDiffAt_map_inverse.comp J contDiffAt_fst
  unfold scalarMetricTraceTwoJet
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt.comp J
    (hI.clm_apply contDiffAt_const)).mul (contDiffAt_jetRicci hJ _ _)

/-- On actual metric data the native two-jet trace is the retained scalar
curvature, with its fixed sign (equation (3.7), p. 41). -/
theorem scalarMetricTraceTwoJet_metricTwoJet {n : ℕ}
    {g : RiemannianMetric n (E n)} (D : LeviCivitaData g) (x : E n) :
    scalarMetricTraceTwoJet (metricTwoJet g.euclideanCoefficients x) =
      D.scalarCurvature x := by
  rw [scalarMetricTraceTwoJet]
  simp_rw [jetRicci_metricTwoJet D]
  exact (metricTrace_eq_inverse_contraction g x (M13.ricciLinear D x)).symm

end PoincareMT.M32
