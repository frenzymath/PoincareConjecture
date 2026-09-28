import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.JetBounds
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.BilinearJets



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.SpacetimeBounds

abbrev MetricCoefficient (n : ℕ) :=
  EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ

abbrev MetricTwoJet (n : ℕ) := MetricCoefficient n ×
  (EuclideanSpace ℝ (Fin n) →L[ℝ] MetricCoefficient n) ×
  (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] MetricCoefficient n)

def metricTwoJet {n : ℕ} (B : EuclideanSpace ℝ (Fin n) → MetricCoefficient n)
    (x : EuclideanSpace ℝ (Fin n)) : MetricTwoJet n :=
  (B x, fderiv ℝ B x, fderiv ℝ (fderiv ℝ B) x)

def jetChristoffel {n : ℕ} (J : MetricTwoJet n) (u v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := J.1.inverse (metricKoszulCovector J.2.1 u v)

def jetCurvature {n : ℕ} (J : MetricTwoJet n) (u w v z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (2⁻¹ : ℝ) * (J.2.2 u z w v - J.2.2 u v w z - J.2.2 w z u v + J.2.2 w v u z) +
    (-J.2.1 u (jetChristoffel J w z) v + J.2.1 w (jetChristoffel J u z) v +
      J.1 (jetChristoffel J u (jetChristoffel J w z)) v -
      J.1 (jetChristoffel J w (jetChristoffel J u z)) v)

def jetRicci {n : ℕ} (J : MetricTwoJet n) (u v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, ∑ j, EuclideanSpace.proj j (J.1.inverse (EuclideanSpace.proj i)) *
    jetCurvature J u (EuclideanSpace.basisFun (Fin n) ℝ i) v
      (EuclideanSpace.basisFun (Fin n) ℝ j)


def ricciFlowOperator (n : ℕ) (J : MetricTwoJet n) : MetricCoefficient n :=
  ∑ i, ∑ j, (-2 * jetRicci J (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)) •
      (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).smulRight
        (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j))

theorem contDiffAt_jetChristoffel {n : ℕ} {J : MetricTwoJet n} (hJ : J.1.IsInvertible)
    {u v : MetricTwoJet n → EuclideanSpace ℝ (Fin n)}
    (hu : ContDiffAt ℝ ∞ u J) (hv : ContDiffAt ℝ ∞ v J) :
    ContDiffAt ℝ ∞ (fun K => jetChristoffel K (u K) (v K)) J := by
  let E := EuclideanSpace ℝ (Fin n)
  have hI : ContDiffAt ℝ ∞ (fun K : MetricTwoJet n => K.1.inverse) J :=
    hJ.contDiffAt_map_inverse.comp J contDiffAt_fst
  have hf : ContDiff ℝ ∞ (fun A : E →L[ℝ] E →L[ℝ] ℝ => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).contDiff
  have hf' : ContDiff ℝ ∞ (fun A : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).contDiff
  unfold jetChristoffel metricKoszulCovector
  fun_prop

theorem contDiffAt_jetCurvature {n : ℕ} {J : MetricTwoJet n} (hJ : J.1.IsInvertible)
    (u w v z : EuclideanSpace ℝ (Fin n)) :
    ContDiffAt ℝ ∞ (fun K => jetCurvature K u w v z) J := by
  have hΓ (a b : EuclideanSpace ℝ (Fin n)) :
      ContDiffAt ℝ ∞ (fun K => jetChristoffel K a b) J :=
    contDiffAt_jetChristoffel hJ contDiffAt_const contDiffAt_const
  have hΓΓ (a b c : EuclideanSpace ℝ (Fin n)) :
      ContDiffAt ℝ ∞ (fun K => jetChristoffel K a (jetChristoffel K b c)) J :=
    contDiffAt_jetChristoffel hJ contDiffAt_const (hΓ b c)
  unfold jetCurvature
  fun_prop

theorem contDiffAt_jetRicci {n : ℕ} {J : MetricTwoJet n} (hJ : J.1.IsInvertible)
    (u v : EuclideanSpace ℝ (Fin n)) :
    ContDiffAt ℝ ∞ (fun K => jetRicci K u v) J := by
  have hI : ContDiffAt ℝ ∞ (fun K : MetricTwoJet n => K.1.inverse) J :=
    hJ.contDiffAt_map_inverse.comp J contDiffAt_fst
  unfold jetRicci
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt.comp J
    (hI.clm_apply contDiffAt_const)).mul (contDiffAt_jetCurvature hJ _ _ _ _)

theorem isOpen_ricciFlowOperator_domain (n : ℕ) :
    IsOpen {J : MetricTwoJet n | J.1.IsInvertible} :=
  ContinuousLinearEquiv.isOpen.preimage continuous_fst

theorem contDiffOn_ricciFlowOperator (n : ℕ) :
    ContDiffOn ℝ ∞ (ricciFlowOperator n) {J : MetricTwoJet n | J.1.IsInvertible} := by
  intro J hJ
  apply ContDiffAt.contDiffWithinAt
  unfold ricciFlowOperator
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (contDiffAt_const.mul (contDiffAt_jetRicci hJ _ _)).smul contDiffAt_const

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem jetChristoffel_metricTwoJet {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    jetChristoffel (metricTwoJet g.euclideanCoefficients x) u v = D.euclideanConnection u v x :=
  (D.connection_const_eq_inverse x u v).symm

theorem jetCurvature_metricTwoJet {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x u w v z : EuclideanSpace ℝ (Fin n)) :
    jetCurvature (metricTwoJet g.euclideanCoefficients x) u w v z =
      D.curvatureTensor x u w v z := by
  rw [D.curvatureTensor_eq_metric_second_deriv]
  simp only [jetCurvature, jetChristoffel_metricTwoJet D]
  rfl

theorem jetRicci_metricTwoJet {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    jetRicci (metricTwoJet g.euclideanCoefficients x) u v = D.ricci x u v := by
  rw [D.ricci_eq_sum_inverseCoefficients_curvatureTensor]
  simp only [jetRicci, jetCurvature_metricTwoJet D,
    RiemannianMetric.inverseCoefficients]
  rfl

end PoincareConjecture.SpacetimeBounds
