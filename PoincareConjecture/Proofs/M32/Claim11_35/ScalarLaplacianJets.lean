import PoincareConjecture.Proofs.M32.Claim11_35.ScalarJets
import PoincareConjecture.Proofs.M32.Mathlib.SecondDerivative
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Laplacian.Harmonic













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M32

open PoincareConjecture.SpacetimeBounds

local notation "E" n:max => EuclideanSpace ℝ (Fin n)



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



abbrev ScalarMetricFourJet (n : ℕ) := MetricTwoJet n ×
  (E n →L[ℝ] MetricTwoJet n) × (E n →L[ℝ] E n →L[ℝ] MetricTwoJet n)


noncomputable local instance scalarFourJetNormedGroup (n : ℕ) :
    NormedAddCommGroup (ScalarMetricFourJet n) := Prod.normedAddCommGroup


noncomputable local instance scalarFourJetNormedSpace (n : ℕ) :
    NormedSpace ℝ (ScalarMetricFourJet n) := Prod.normedSpace


noncomputable def scalarMetricFourJet {n : ℕ} (B : E n → MetricCoefficient n)
    (x : E n) : ScalarMetricFourJet n :=
  (metricTwoJet B x, fderiv ℝ (metricTwoJet B) x,
    fderiv ℝ (fderiv ℝ (metricTwoJet B)) x)



noncomputable def scalarContractedChristoffel {n : ℕ} (J : MetricTwoJet n) : E n :=
  ∑ i, jetChristoffel J (EuclideanSpace.basisFun (Fin n) ℝ i)
    (J.1.inverse (EuclideanSpace.proj i))



noncomputable def scalarLaplacianFourJet {n : ℕ} (K : ScalarMetricFourJet n) : ℝ :=
  (∑ i, (fderiv ℝ (fderiv ℝ (@scalarMetricTraceTwoJet n)) K.1
      (K.2.1 (EuclideanSpace.basisFun (Fin n) ℝ i))
      (K.2.1 (K.1.1.inverse (EuclideanSpace.proj i))) +
    fderiv ℝ (@scalarMetricTraceTwoJet n) K.1
      (K.2.2 (EuclideanSpace.basisFun (Fin n) ℝ i)
        (K.1.1.inverse (EuclideanSpace.proj i))))) -
  fderiv ℝ (@scalarMetricTraceTwoJet n) K.1 (K.2.1 (scalarContractedChristoffel K.1))



theorem contDiffAt_metricTwoJet {n : ℕ} {B : E n → MetricCoefficient n} {x : E n}
    (hB : ContDiffAt ℝ ∞ B x) : ContDiffAt ℝ ∞ (metricTwoJet B) x := by
  have hB' := hB.fderiv_right (m := ∞) (by simp)
  exact hB.prodMk (hB'.prodMk (hB'.fderiv_right (m := ∞) (by simp)))



theorem contDiffAt_scalarContractedChristoffel {n : ℕ} {J : MetricTwoJet n}
    (hJ : J.1.IsInvertible) : ContDiffAt ℝ ∞ (@scalarContractedChristoffel n) J := by
  have hI : ContDiffAt ℝ ∞ (fun K : MetricTwoJet n => K.1.inverse) J :=
    hJ.contDiffAt_map_inverse.comp J contDiffAt_fst
  apply ContDiffAt.sum
  intro i _
  exact contDiffAt_jetChristoffel hJ contDiffAt_const (hI.clm_apply contDiffAt_const)

set_option maxHeartbeats 800000 in



theorem continuousAt_scalarLaplacianFourJet {n : ℕ} {K : ScalarMetricFourJet n}
    (hK : K.1.1.IsInvertible) : ContinuousAt (@scalarLaplacianFourJet n) K := by
  have hInv : ContDiffAt ℝ ∞ (fun L : MetricTwoJet n => L.1.inverse) K.1 :=
    hK.contDiffAt_map_inverse.comp K.1 contDiffAt_fst
  have hI (i : Fin n) : ContinuousAt (fun L : ScalarMetricFourJet n =>
      L.1.1.inverse (EuclideanSpace.proj i)) K :=
    (hInv.continuousAt.comp continuousAt_fst).clm_apply continuousAt_const
  have hC : ContinuousAt (fun L : ScalarMetricFourJet n =>
      scalarContractedChristoffel L.1) K :=
    (contDiffAt_scalarContractedChristoffel hK).continuousAt.comp continuousAt_fst
  unfold scalarLaplacianFourJet
  exact continuousAt_secondDerivativeContraction (EuclideanSpace.basisFun (Fin n) ℝ)
    (contDiffAt_scalarMetricTraceTwoJet hK) continuousAt_fst
    continuousAt_snd.fst continuousAt_snd.snd hI hC

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace

set_option maxHeartbeats 800000 in



theorem scalarLaplacianFourJet_scalarMetricFourJet {n : ℕ}
    {g : RiemannianMetric n (E n)} (D : LeviCivitaData g) (x : E n) :
    scalarLaplacianFourJet (scalarMetricFourJet g.euclideanCoefficients x) =
      D.laplacian D.scalarCurvature x := by
  let J := metricTwoJet g.euclideanCoefficients
  have hJ : ContDiffAt ℝ ∞ J x :=
    contDiffAt_metricTwoJet (g.contDiffAt_euclideanCoefficients x)
  have hS : ContDiffAt ℝ ∞ (@scalarMetricTraceTwoJet n) (J x) :=
    contDiffAt_scalarMetricTraceTwoJet (g.inner_isInvertible x)
  have heq : scalarMetricTraceTwoJet ∘ J = D.scalarCurvature :=
    funext fun y => scalarMetricTraceTwoJet_metricTwoJet D y
  have hR : ContDiffAt ℝ ∞ D.scalarCurvature x := heq ▸ hS.comp x hJ
  have hfirst : fderiv ℝ D.scalarCurvature x =
      (fderiv ℝ (@scalarMetricTraceTwoJet n) (J x)).comp (fderiv ℝ J x) := by
    rw [← heq]
    exact fderiv_comp x (hS.differentiableAt (by simp)) (hJ.differentiableAt (by simp))
  have hsecond (u v : E n) : fderiv ℝ (fderiv ℝ D.scalarCurvature) x u v =
      fderiv ℝ (fderiv ℝ (@scalarMetricTraceTwoJet n)) (J x)
        (fderiv ℝ J x u) (fderiv ℝ J x v) +
      fderiv ℝ (@scalarMetricTraceTwoJet n) (J x) (fderiv ℝ (fderiv ℝ J) x u v) := by
    simpa only [heq] using second_fderiv_comp_of_contDiffAt hJ hS u v
  rw [D.laplacian_eq_sum_fderiv_sub_christoffel hR]
  simp_rw [hsecond]
  rw [hfirst]
  rfl

end PoincareConjecture.M32
