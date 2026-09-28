import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarJet
import PoincareConjecture.Proofs.M44.Mathlib.SecondDerivativeComposition
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Laplacian.Harmonic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M44

open PoincareConjecture.SpacetimeBounds

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

abbrev ScalarMetricFourJet (n : ℕ) := MetricTwoJet n ×
  (Fin n → MetricTwoJet n) × (Fin n → Fin n → MetricTwoJet n)

noncomputable def scalarMetricFourJet {n : ℕ} (B : E n → MetricCoefficient n)
    (x : E n) : ScalarMetricFourJet n :=
  (metricTwoJet B x,
    fun i => fderiv ℝ (metricTwoJet B) x (EuclideanSpace.basisFun (Fin n) ℝ i),
    fun i j => fderiv ℝ (fderiv ℝ (metricTwoJet B)) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j))

theorem contDiffAt_metricTwoJet {n : ℕ} {B : E n → MetricCoefficient n} {x : E n}
    (hB : ContDiffAt ℝ ∞ B x) : ContDiffAt ℝ ∞ (metricTwoJet B) x := by
  have hB' := hB.fderiv_right (m := ∞) (by simp)
  exact hB.prodMk (hB'.prodMk (hB'.fderiv_right (m := ∞) (by simp)))

noncomputable def jetScalarFirst {n : ℕ} (K : ScalarMetricFourJet n) (i : Fin n) : ℝ :=
  fderiv ℝ (@jetScalarCurvature n) K.1 (K.2.1 i)

noncomputable def jetScalarSecond {n : ℕ} (K : ScalarMetricFourJet n)
    (i j : Fin n) : ℝ :=
  fderiv ℝ (fderiv ℝ (@jetScalarCurvature n)) K.1 (K.2.1 i) (K.2.1 j) +
    fderiv ℝ (@jetScalarCurvature n) K.1 (K.2.2 i j)

noncomputable def jetContractedChristoffel {n : ℕ} (J : MetricTwoJet n) : E n :=
  ∑ i, jetChristoffel J (EuclideanSpace.basisFun (Fin n) ℝ i)
    (J.1.inverse (EuclideanSpace.proj i))

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

theorem contDiffAt_jetContractedChristoffel {n : ℕ} {J : MetricTwoJet n}
    (hJ : J.1.IsInvertible) : ContDiffAt ℝ ∞ (@jetContractedChristoffel n) J := by
  have hI : ContDiffAt ℝ ∞ (fun K : MetricTwoJet n => K.1.inverse) J :=
    hJ.contDiffAt_map_inverse.comp J contDiffAt_fst
  apply ContDiffAt.sum
  intro i _
  exact contDiffAt_jetChristoffel hJ contDiffAt_const (hI.clm_apply contDiffAt_const)

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

end PoincareConjecture.M44
