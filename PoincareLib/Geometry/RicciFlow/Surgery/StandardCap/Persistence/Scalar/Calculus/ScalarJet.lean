import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Homothety
import PoincareLib.Geometry.Riemannian.Homothety.Curvature.Contractions
import PoincareLib.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.Operator
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Scalar curvature as a smooth function of the actual metric two-jet

The inverse-metric contraction of the published Ricci operator is the
actual scalar curvature. This is the finite-calculus input to the
neck and round estimates in the forward use of Lemma 11.2.
Morgan--Tian, equation (3.7), p. 41, and Lemma 16.8, pp. 372-373;
see derivation 26.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The metric two-jet has four nested continuous-linear slots.
set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareMT.M44

open PoincareMT.SpacetimeBounds

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

/-- The metric trace of an arbitrary bilinear form in the fixed
Euclidean coordinates. No smooth choice of orthonormal basis is used.
Source: the scalar contraction in equation (3.7), p. 41. -/
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

/-- The scalar-curvature contraction of the native metric two-jet.
Its geometric use is restricted to invertible positive metric germs.
Source: equation (3.7), p. 41, in the proof of Lemma 16.8. -/
noncomputable def jetScalarCurvature {n : ℕ} (J : MetricTwoJet n) : ℝ :=
  ∑ i, ∑ j, EuclideanSpace.proj j (J.1.inverse (EuclideanSpace.proj i)) *
    jetRicci J (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)

/-- Scalar curvature depends smoothly on the two-jet wherever the
metric coefficient is invertible. Source: the finite metric-jet
calculation in Lemma 16.8, pp. 372-373. -/
theorem contDiffAt_jetScalarCurvature {n : ℕ} {J : MetricTwoJet n}
    (hJ : J.1.IsInvertible) : ContDiffAt ℝ ∞ (@jetScalarCurvature n) J := by
  have hI : ContDiffAt ℝ ∞ (fun K : MetricTwoJet n => K.1.inverse) J :=
    hJ.contDiffAt_map_inverse.comp J contDiffAt_fst
  unfold jetScalarCurvature
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt.comp J
    (hI.clm_apply contDiffAt_const)).mul (contDiffAt_jetRicci hJ _ _)

/-- Inverse-metric evaluation is continuous in the native two-jet
space. Source: the scalar Laplacian contraction in equation (3.7). -/
theorem continuousAt_jetInverse_apply {n : ℕ} {J : MetricTwoJet n}
    (hJ : J.1.IsInvertible) (v : E n →L[ℝ] ℝ) :
    ContinuousAt (fun K : MetricTwoJet n => K.1.inverse v) J := by
  have hI : ContDiffAt ℝ ∞ (fun K : MetricTwoJet n => K.1.inverse) J :=
    hJ.contDiffAt_map_inverse.comp J contDiffAt_fst
  exact hI.continuousAt.clm_apply continuousAt_const

/-- The native scalar operator is the actual scalar curvature for
every smooth positive metric. Source: equation (3.7), p. 41. -/
theorem jetScalarCurvature_metricTwoJet {n : ℕ}
    {g : RiemannianMetric n (E n)} (D : LeviCivitaData g) (x : E n) :
    jetScalarCurvature (metricTwoJet g.euclideanCoefficients x) = D.scalarCurvature x := by
  rw [jetScalarCurvature]
  simp_rw [jetRicci_metricTwoJet D]
  exact (metricTrace_eq_inverse_contraction g x (M13.ricciLinear D x)).symm

/-- The actual scalar field is smooth in fixed Euclidean coordinates.
This follows from the actual metric formula without choosing a moving
orthonormal frame. Source: equation (3.7), p. 41. -/
theorem contDiff_scalarCurvature {n : ℕ}
    {g : RiemannianMetric n (E n)} (D : LeviCivitaData g) :
    ContDiff ℝ ∞ D.scalarCurvature := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hB := g.contDiffAt_euclideanCoefficients x
  have hB' := hB.fderiv_right (m := ∞) (by simp)
  have hB'' := hB'.fderiv_right (m := ∞) (by simp)
  have hJ : ContDiffAt ℝ ∞ (metricTwoJet g.euclideanCoefficients) x :=
    hB.prodMk (hB'.prodMk hB'')
  have h := (contDiffAt_jetScalarCurvature (g.inner_isInvertible x)).comp x hJ
  simpa only [Function.comp_def, jetScalarCurvature_metricTwoJet D] using h

end PoincareMT.M44
