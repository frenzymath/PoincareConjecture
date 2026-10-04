import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.AncientLimits.Scalar.ScalarJets
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Calculus.SecondDerivative
import PoincareLib.Geometry.Riemannian.ScalarOperators.Laplacian.Harmonic

/-!
# The actual scalar Laplacian as a four-jet readout

Morgan--Tian equation (3.7), printed p. 41, and Claim 11.35, pp. 289-291.
The full linear slots retain derivatives through order four. Twice applying
the chain rule identifies the readout with the actual signed Laplacian.

Locally re-derived from read-only M44 Sec16_1_CapPersistence/
Lemma11_2_ScalarFourJet, using full linear maps instead of coordinate arrays.
No later proof is imported. Derivation: `claim11_35-scalar-laplacian-jets.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

open scoped Manifold ContDiff Topology BigOperators

namespace PoincareMT.M32

open PoincareMT.SpacetimeBounds

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

-- Cache the nested native operator instances used in the full jet slots.
/-- The native coefficient norm in the finite calculus of equation (3.7), p. 41. -/
noncomputable local instance scalarCoefficientNormedGroup (n : ℕ) :
    NormedAddCommGroup (MetricCoefficient n) := ContinuousLinearMap.toNormedAddCommGroup

/-- The native coefficient scalar action for equation (3.7), printed p. 41. -/
noncomputable local instance scalarCoefficientNormedSpace (n : ℕ) :
    NormedSpace ℝ (MetricCoefficient n) := ContinuousLinearMap.toNormedSpace

/-- The native two-jet max norm for equation (3.7), printed p. 41. -/
noncomputable local instance scalarTwoJetNormedGroup (n : ℕ) :
    NormedAddCommGroup (MetricTwoJet n) := Prod.normedAddCommGroup

/-- The native two-jet scalar action for equation (3.7), printed p. 41. -/
noncomputable local instance scalarTwoJetNormedSpace (n : ℕ) :
    NormedSpace ℝ (MetricTwoJet n) := Prod.normedSpace

/-- The native first-jet operator norm for equation (3.7), printed p. 41. -/
noncomputable local instance scalarTwoJetFirstNormedGroup (n : ℕ) :
    NormedAddCommGroup (E n →L[ℝ] MetricTwoJet n) := ContinuousLinearMap.toNormedAddCommGroup

/-- The native first-jet scalar action for equation (3.7), printed p. 41. -/
noncomputable local instance scalarTwoJetFirstNormedSpace (n : ℕ) :
    NormedSpace ℝ (E n →L[ℝ] MetricTwoJet n) := ContinuousLinearMap.toNormedSpace

/-- The native second-jet operator norm for equation (3.7), printed p. 41. -/
noncomputable local instance scalarTwoJetSecondNormedGroup (n : ℕ) :
    NormedAddCommGroup (E n →L[ℝ] E n →L[ℝ] MetricTwoJet n) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The native second-jet scalar action for equation (3.7), printed p. 41. -/
noncomputable local instance scalarTwoJetSecondNormedSpace (n : ℕ) :
    NormedSpace ℝ (E n →L[ℝ] E n →L[ℝ] MetricTwoJet n) := ContinuousLinearMap.toNormedSpace

/-- Full first and second derivatives of the metric two-jet, as required
for the scalar evolution calculation in Claim 11.35, printed p. 289. -/
abbrev ScalarMetricFourJet (n : ℕ) := MetricTwoJet n ×
  (E n →L[ℝ] MetricTwoJet n) × (E n →L[ℝ] E n →L[ℝ] MetricTwoJet n)

/-- The native full-jet max norm for the Laplacian in equation (3.7), p. 41. -/
noncomputable local instance scalarFourJetNormedGroup (n : ℕ) :
    NormedAddCommGroup (ScalarMetricFourJet n) := Prod.normedAddCommGroup

/-- The native full-jet scalar action for equation (3.7), printed p. 41. -/
noncomputable local instance scalarFourJetNormedSpace (n : ℕ) :
    NormedSpace ℝ (ScalarMetricFourJet n) := Prod.normedSpace

/-- The actual metric data through order four; equation (3.7), p. 41. -/
noncomputable def scalarMetricFourJet {n : ℕ} (B : E n → MetricCoefficient n)
    (x : E n) : ScalarMetricFourJet n :=
  (metricTwoJet B x, fderiv ℝ (metricTwoJet B) x,
    fderiv ℝ (fderiv ℝ (metricTwoJet B)) x)

/-- The inverse-metric contraction of the connection correction in
the scalar Laplacian; equation (3.7), printed p. 41. -/
noncomputable def scalarContractedChristoffel {n : ℕ} (J : MetricTwoJet n) : E n :=
  ∑ i, jetChristoffel J (EuclideanSpace.basisFun (Fin n) ℝ i)
    (J.1.inverse (EuclideanSpace.proj i))

/-- The chain-rule readout with the signed connection correction;
equation (3.7), p. 41, used in Claim 11.35, p. 289. -/
noncomputable def scalarLaplacianFourJet {n : ℕ} (K : ScalarMetricFourJet n) : ℝ :=
  (∑ i, (fderiv ℝ (fderiv ℝ (@scalarMetricTraceTwoJet n)) K.1
      (K.2.1 (EuclideanSpace.basisFun (Fin n) ℝ i))
      (K.2.1 (K.1.1.inverse (EuclideanSpace.proj i))) +
    fderiv ℝ (@scalarMetricTraceTwoJet n) K.1
      (K.2.2 (EuclideanSpace.basisFun (Fin n) ℝ i)
        (K.1.1.inverse (EuclideanSpace.proj i))))) -
  fderiv ℝ (@scalarMetricTraceTwoJet n) K.1 (K.2.1 (scalarContractedChristoffel K.1))

/-- Smooth metric coefficients give a smooth two-jet field, as used in
the twice differentiated scalar identity of Claim 11.35, p. 289. -/
theorem contDiffAt_metricTwoJet {n : ℕ} {B : E n → MetricCoefficient n} {x : E n}
    (hB : ContDiffAt ℝ ∞ B x) : ContDiffAt ℝ ∞ (metricTwoJet B) x := by
  have hB' := hB.fderiv_right (m := ∞) (by simp)
  exact hB.prodMk (hB'.prodMk (hB'.fderiv_right (m := ∞) (by simp)))

/-- The connection contraction is smooth where the zeroth metric is
invertible; the signed scalar calculation is equation (3.7), p. 41. -/
theorem contDiffAt_scalarContractedChristoffel {n : ℕ} {J : MetricTwoJet n}
    (hJ : J.1.IsInvertible) : ContDiffAt ℝ ∞ (@scalarContractedChristoffel n) J := by
  have hI : ContDiffAt ℝ ∞ (fun K : MetricTwoJet n => K.1.inverse) J :=
    hJ.contDiffAt_map_inverse.comp J contDiffAt_fst
  apply ContDiffAt.sum
  intro i _
  exact contDiffAt_jetChristoffel hJ contDiffAt_const (hI.clm_apply contDiffAt_const)

set_option maxHeartbeats 800000 in
-- The kernel compares the native normed instances of the full jet slots.
/-- The Laplacian readout is continuous on the invertible domain, with
no consistency hypothesis on the higher formal slots; Claim 11.35, p. 289. -/
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
-- The actual chain rule compares native tangent and nested jet instances.
/-- The readout is the actual retained scalar Laplacian, with the sign
in equation (3.7), p. 41; this is the static step in Claim 11.35, p. 289. -/
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

end PoincareMT.M32
