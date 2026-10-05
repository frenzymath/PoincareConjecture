import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scalar.Calculus.ScalarJet
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Analysis.Jets.SecondDerivativeComposition
import PoincareLib.Geometry.Riemannian.ScalarOperators.Laplacian.Harmonic

/-!
# The actual scalar Laplacian from four metric derivatives

The chain rule differentiates the native two-jet scalar operator twice.
The inverse-metric trace and Christoffel correction give the actual
Laplacian, including its sign. Morgan--Tian, equation (3.7), p. 41,
and the forward estimate in Lemma 16.8, pp. 372-373; derivation 26.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The two-jet scalar derivative still has nested continuous-linear slots.
set_option maxSynthPendingDepth 16

open Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareMT.M44

open PoincareMT.SpacetimeBounds

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

/-- The two-jet field and its first two derivatives on the coordinate
basis. This redundant jet stores the metric derivatives through order four.
Source: the finite-jet scalar estimate in Lemma 16.8, pp. 372-373. -/
abbrev ScalarMetricFourJet (n : ℕ) := MetricTwoJet n ×
  (Fin n → MetricTwoJet n) × (Fin n → Fin n → MetricTwoJet n)

/-- The actual four-jet data used by the scalar Laplacian operator.
Only smooth germs with invertible zeroth metric enter its geometric use.
Source: equation (3.7), p. 41. -/
noncomputable def scalarMetricFourJet {n : ℕ} (B : E n → MetricCoefficient n)
    (x : E n) : ScalarMetricFourJet n :=
  (metricTwoJet B x,
    fun i => fderiv ℝ (metricTwoJet B) x (EuclideanSpace.basisFun (Fin n) ℝ i),
    fun i j => fderiv ℝ (fderiv ℝ (metricTwoJet B)) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j))

/-- Smooth metric coefficients give a smooth native two-jet field.
Source: the finite-jet calculation in Lemma 16.8, pp. 372-373. -/
theorem contDiffAt_metricTwoJet {n : ℕ} {B : E n → MetricCoefficient n} {x : E n}
    (hB : ContDiffAt ℝ ∞ B x) : ContDiffAt ℝ ∞ (metricTwoJet B) x := by
  have hB' := hB.fderiv_right (m := ∞) (by simp)
  exact hB.prodMk (hB'.prodMk (hB'.fderiv_right (m := ∞) (by simp)))

/-- The chain-rule first scalar derivative on one coordinate direction.
Source: equation (3.7), p. 41. -/
noncomputable def jetScalarFirst {n : ℕ} (K : ScalarMetricFourJet n) (i : Fin n) : ℝ :=
  fderiv ℝ (@jetScalarCurvature n) K.1 (K.2.1 i)

/-- The chain-rule second scalar derivative in two fixed directions.
Source: equation (3.7), p. 41. -/
noncomputable def jetScalarSecond {n : ℕ} (K : ScalarMetricFourJet n)
    (i j : Fin n) : ℝ :=
  fderiv ℝ (fderiv ℝ (@jetScalarCurvature n)) K.1 (K.2.1 i) (K.2.1 j) +
    fderiv ℝ (@jetScalarCurvature n) K.1 (K.2.2 i j)

/-- The inverse-metric contraction of the Christoffel symbol.
Source: the coordinate Laplacian in equation (3.7), p. 41. -/
noncomputable def jetContractedChristoffel {n : ℕ} (J : MetricTwoJet n) : E n :=
  ∑ i, jetChristoffel J (EuclideanSpace.basisFun (Fin n) ℝ i)
    (J.1.inverse (EuclideanSpace.proj i))

/-- The scalar Laplacian computed from the actual four-jet data.
The minus sign is the connection correction in the scalar Hessian.
Source: equation (3.7), p. 41. -/
noncomputable def jetScalarLaplacian {n : ℕ} (K : ScalarMetricFourJet n) : ℝ :=
  secondDerivativeArrayContraction (@jetScalarCurvature n)
    (fun L : ScalarMetricFourJet n => L.1)
    (fun i (L : ScalarMetricFourJet n) => L.2.1 i)
    (fun i j (L : ScalarMetricFourJet n) => L.2.2 i j)
    (fun i j (L : ScalarMetricFourJet n) =>
      EuclideanSpace.proj j (L.1.1.inverse (EuclideanSpace.proj i)))
    (fun i (L : ScalarMetricFourJet n) => EuclideanSpace.proj i (jetContractedChristoffel L.1)) K

section ChainRule

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace

-- Cache only the geometric chain rule; the operator keeps the native instances.
noncomputable local instance scalarCoefficientNormedGroup (n : ℕ) :
    NormedAddCommGroup (MetricCoefficient n) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance scalarCoefficientNormedSpace (n : ℕ) :
    NormedSpace ℝ (MetricCoefficient n) := ContinuousLinearMap.toNormedSpace

noncomputable local instance scalarTwoJetNormedGroup (n : ℕ) :
    NormedAddCommGroup (MetricTwoJet n) := Prod.normedAddCommGroup

noncomputable local instance scalarTwoJetNormedSpace (n : ℕ) :
    NormedSpace ℝ (MetricTwoJet n) := Prod.normedSpace

noncomputable local instance scalarTwoJetFirstNormedGroup (n : ℕ) :
    NormedAddCommGroup (E n →L[ℝ] MetricTwoJet n) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance scalarTwoJetFirstNormedSpace (n : ℕ) :
    NormedSpace ℝ (E n →L[ℝ] MetricTwoJet n) := ContinuousLinearMap.toNormedSpace

noncomputable local instance scalarTwoJetSecondNormedGroup (n : ℕ) :
    NormedAddCommGroup (E n →L[ℝ] E n →L[ℝ] MetricTwoJet n) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance scalarTwoJetSecondNormedSpace (n : ℕ) :
    NormedSpace ℝ (E n →L[ℝ] E n →L[ℝ] MetricTwoJet n) := ContinuousLinearMap.toNormedSpace

/-- The native first scalar derivative equals the derivative of the
actual scalar field. Source: equation (3.7), p. 41. -/
theorem jetScalarFirst_scalarMetricFourJet {n : ℕ}
    {g : RiemannianMetric n (E n)} (D : LeviCivitaData g) (x : E n) (i : Fin n) :
    jetScalarFirst (scalarMetricFourJet g.euclideanCoefficients x) i =
      fderiv ℝ D.scalarCurvature x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  have hJ := contDiffAt_metricTwoJet (g.contDiffAt_euclideanCoefficients x)
  have hS : ContDiffAt ℝ ∞ (@jetScalarCurvature n)
      (metricTwoJet g.euclideanCoefficients x) :=
    contDiffAt_jetScalarCurvature (g.inner_isInvertible x)
  have heq : D.scalarCurvature = jetScalarCurvature ∘ metricTwoJet g.euclideanCoefficients :=
    funext fun y => (jetScalarCurvature_metricTwoJet D y).symm
  rw [heq, fderiv_comp x (hS.differentiableAt (by simp)) (hJ.differentiableAt (by simp))]
  rfl

/-- The native second scalar derivative equals the actual second
coordinate derivative. Source: equation (3.7), p. 41. -/
theorem jetScalarSecond_scalarMetricFourJet {n : ℕ}
    {g : RiemannianMetric n (E n)} (D : LeviCivitaData g) (x : E n) (i j : Fin n) :
    jetScalarSecond (scalarMetricFourJet g.euclideanCoefficients x) i j =
      fderiv ℝ (fderiv ℝ D.scalarCurvature) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  let J := metricTwoJet g.euclideanCoefficients
  have hJ : ContDiffAt ℝ ∞ J x :=
    contDiffAt_metricTwoJet (g.contDiffAt_euclideanCoefficients x)
  have hS : ContDiffAt ℝ ∞ (@jetScalarCurvature n) (J x) :=
    contDiffAt_jetScalarCurvature (g.inner_isInvertible x)
  have h := second_fderiv_comp_of_contDiffAt hJ hS
    (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)
  have heq : jetScalarCurvature ∘ J = D.scalarCurvature :=
    funext fun y => jetScalarCurvature_metricTwoJet D y
  rw [heq] at h
  exact h.symm

/-- The finite-jet operator equals the actual scalar Laplacian at a
smooth metric germ. Source: equation (3.7), p. 41. -/
theorem jetScalarLaplacian_scalarMetricFourJet {n : ℕ}
    {g : RiemannianMetric n (E n)} (D : LeviCivitaData g) (x : E n) :
    jetScalarLaplacian (scalarMetricFourJet g.euclideanCoefficients x) =
      D.laplacian D.scalarCurvature x := by
  have hlap : D.laplacian D.scalarCurvature x =
      (∑ i, fderiv ℝ (fderiv ℝ D.scalarCurvature) x (EuclideanSpace.basisFun (Fin n) ℝ i)
        ((g.euclideanCoefficients x).inverse (EuclideanSpace.proj i))) -
      fderiv ℝ D.scalarCurvature x (∑ i, CoordinateExponential.christoffelBilinear
        g.euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ i)
        ((g.euclideanCoefficients x).inverse (EuclideanSpace.proj i))) :=
    D.laplacian_eq_sum_fderiv_sub_christoffel (contDiff_scalarCurvature D).contDiffAt
  rw [hlap]
  have hchrist : jetContractedChristoffel (scalarMetricFourJet g.euclideanCoefficients x).1 =
      ∑ i, CoordinateExponential.christoffelBilinear g.euclideanCoefficients x
        (EuclideanSpace.basisFun (Fin n) ℝ i)
        ((g.euclideanCoefficients x).inverse (EuclideanSpace.proj i)) := by
    unfold jetContractedChristoffel
    apply Finset.sum_congr rfl
    intro i hi
    change jetChristoffel (metricTwoJet g.euclideanCoefficients x)
      (EuclideanSpace.basisFun (Fin n) ℝ i)
      ((g.euclideanCoefficients x).inverse (EuclideanSpace.proj i)) = _
    rw [jetChristoffel_metricTwoJet D]
    simp only [LeviCivitaData.euclideanConnection]
    rw [D.connection_const_eq_inverse]
    rfl
  change (∑ i, ∑ j,
    EuclideanSpace.proj j ((g.euclideanCoefficients x).inverse (EuclideanSpace.proj i)) *
      jetScalarSecond (scalarMetricFourJet g.euclideanCoefficients x) i j) -
    (∑ i, EuclideanSpace.proj i
      (jetContractedChristoffel (scalarMetricFourJet g.euclideanCoefficients x).1) *
      jetScalarFirst (scalarMetricFourJet g.euclideanCoefficients x) i) = _
  simp_rw [jetScalarFirst_scalarMetricFourJet D, jetScalarSecond_scalarMetricFourJet D]
  rw [hchrist]
  have hread (L : E n →L[ℝ] ℝ) (v : E n) :
      (∑ j, EuclideanSpace.proj j v * L (EuclideanSpace.basisFun (Fin n) ℝ j)) = L v := by
    have h := congrArg L ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v)
    simpa only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      PiLp.proj_apply] using h
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact hread _ _
  · exact hread _ _

end ChainRule

/-- The contracted Christoffel symbol is smooth on invertible metric
two-jets. Source: the scalar Laplacian calculation in Lemma 16.8. -/
theorem contDiffAt_jetContractedChristoffel {n : ℕ} {J : MetricTwoJet n}
    (hJ : J.1.IsInvertible) : ContDiffAt ℝ ∞ (@jetContractedChristoffel n) J := by
  have hI : ContDiffAt ℝ ∞ (fun K : MetricTwoJet n => K.1.inverse) J :=
    hJ.contDiffAt_map_inverse.comp J contDiffAt_fst
  apply ContDiffAt.sum
  intro i _
  exact contDiffAt_jetChristoffel hJ contDiffAt_const (hI.clm_apply contDiffAt_const)

/-- The scalar Laplacian is continuous on four-jet data with invertible
metric coefficient. No consistency condition on the remaining jet
slots is needed for this analytic assertion. Source: Lemma 16.8. -/
theorem continuousAt_jetScalarLaplacian {n : ℕ} {K : ScalarMetricFourJet n}
    (hK : K.1.1.IsInvertible) : ContinuousAt (@jetScalarLaplacian n) K := by
  have hA (i : Fin n) : ContinuousAt (fun L : ScalarMetricFourJet n => L.2.1 i) K :=
    (continuous_apply i).continuousAt.comp continuousAt_snd.fst
  have hB (i j : Fin n) : ContinuousAt (fun L : ScalarMetricFourJet n => L.2.2 i j) K :=
    (continuous_apply j).continuousAt.comp
      ((continuous_apply i).continuousAt.comp continuousAt_snd.snd)
  have hC : ContinuousAt (fun L : ScalarMetricFourJet n => jetContractedChristoffel L.1) K :=
    (contDiffAt_jetContractedChristoffel hK).continuousAt.comp continuousAt_fst
  unfold jetScalarLaplacian
  exact continuousAt_secondDerivativeArrayContraction (contDiffAt_jetScalarCurvature hK)
    continuousAt_fst hA hB
    (fun i j => (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.continuousAt.comp
      ((continuousAt_jetInverse_apply hK (EuclideanSpace.proj i)).comp continuousAt_fst))
    (fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.continuousAt.comp hC)

end PoincareMT.M44
