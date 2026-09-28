import PoincareConjecture.Proofs.M34.Standard.CanonicalConnectionDifferenceBound
import PoincareConjecture.Proofs.M34.Standard.CanonicalActualCurvatureBound
import PoincareConjecture.Proofs.M34.Mathlib.EuclideanCoordinateSquareBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

theorem exists_canonicalDomain_differenceDensity_bound
    {n dH dA dS : ℕ} (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (V n)) (hU : IsOpen U) (hNE : Nonempty U),
      letI := hNE
      letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
      ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g)
        (g' : RiemannianMetric n U) (D' : LeviCivitaData g') (p : U) (x : V n), x ∈ U →
        let B0 := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
        let B1 := g'.pullbackCoefficients (extChartAt (𝓡 n) p).symm
        (∀ j ≤ 3, ‖iteratedFDeriv ℝ j B0 x‖ ≤ M) →
        (∀ j ≤ 3, ‖iteratedFDeriv ℝ j B1 x‖ ≤ M) →
        (∀ v, a * ‖v‖ ^ 2 ≤ B0 x v v) →
        (∀ v, a * ‖v‖ ^ 2 ≤ B1 x v v) →
        actualDifferenceEnergyDensity qH qA qS D D'
          ((extChartAt (𝓡 n) p).symm x) ≤ C := by
  obtain ⟨CB, hCB, hback⟩ := canonicalDomain_differenceEnergyBackground_bound n ha M
  obtain ⟨CR, _hCR, hcurv⟩ := exists_canonicalDomain_actualCurvature_norm_bound n ha M
  let cH := ‖qH.toContinuousLinearMap‖ * (2 * M)
  let cA := ‖qA.toContinuousLinearMap‖ * ((n : ℝ) ^ 3 * (2 * CB))
  let cS := ‖qS.toContinuousLinearMap‖ * (2 * CR)
  refine ⟨cH ^ 2 + cA ^ 2 + cS ^ 2, by positivity, ?_⟩
  intro U hU hNE
  let := hNE
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D g' D' p x hx B0 B1 hj0 hj1 he0 he1
  let r := (extChartAt (𝓡 n) p).symm
  let H : FH n := g.inner (r x) - g'.inner (r x)
  let A : FA n := CovariantDerivative.difference D.connection D'.connection (r x)
  let R : FS n := curvatureTrilinearMap D (r x)
  let R' : FS n := curvatureTrilinearMap D' (r x)
  let S : FS n := R - R'
  have hH : ‖H‖ ≤ 2 * M := by
    have hm0 : ‖B0 x‖ ≤ M := by simpa only [norm_iteratedFDeriv_zero] using hj0 0 (by omega)
    have hm1 : ‖B1 x‖ ≤ M := by simpa only [norm_iteratedFDeriv_zero] using hj1 0 (by omega)
    have hh : H = B0 x - B1 x := by
      dsimp only [H, r]
      rw [canonicalDomain_inner_eq_pullbackCoefficients U hU g p x hx,
        canonicalDomain_inner_eq_pullbackCoefficients U hU g' p x hx]
    rw [hh]
    exact (norm_sub_le _ _).trans (by linarith)
  have hb0 := hback U hU hNE g D p x hx hj0 he0
  have hb1 := hback U hU hNE g' D' p x hx hj1 he1
  have hA : ‖A‖ ≤ (n : ℝ) ^ 3 * (2 * CB) :=
    canonicalDomain_connection_difference_norm_le U hU g D g' D' p x
      (zero_le_one.trans hCB) hb0 hb1
  have hR : ‖R‖ ≤ CR := hcurv U hU hNE g D p x hx hj0 he0
  have hR' : ‖R'‖ ≤ CR := hcurv U hU hNE g' D' p x hx hj1 he1
  have hS : ‖S‖ ≤ 2 * CR := (norm_sub_le R R').trans (by linarith)
  change (∑ i, qH H i ^ 2) + (∑ i, qA A i ^ 2) + (∑ i, qS S i ^ 2) ≤ _
  have hsH : (∑ i, qH H i ^ 2) ≤ cH ^ 2 :=
    qH.toContinuousLinearMap.sum_sq_euclidean_apply_le hH
  have hsA : (∑ i, qA A i ^ 2) ≤ cA ^ 2 :=
    qA.toContinuousLinearMap.sum_sq_euclidean_apply_le hA
  have hsS : (∑ i, qS S i ^ 2) ≤ cS ^ 2 :=
    qS.toContinuousLinearMap.sum_sq_euclidean_apply_le hS
  exact add_le_add (add_le_add hsH hsA) hsS

end PoincareConjecture.M34
