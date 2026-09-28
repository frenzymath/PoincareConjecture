import PoincareConjecture.Proofs.M34.Standard.CanonicalDifferenceEnergy
import PoincareConjecture.Proofs.Ch01.CurvatureConnection











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

universe u



theorem actualDifferenceEnergyDensity_eq_zero_of_metric_eq
    {n dH dA dS : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (V n) M] [IsManifold (𝓡 n) ∞ M]
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {g g' : RiemannianMetric n M} (h : g = g')
    (D : LeviCivitaData g) (D' : LeviCivitaData g') (x : M) :
    actualDifferenceEnergyDensity qH qA qS D D' x = 0 := by
  subst g'
  have hR : curvatureTrilinearMap D x = curvatureTrilinearMap D' x := by
    ext u v w
    exact (curvatureTrilinearMap_apply D x u v w).trans
      ((D.curvature_eq D' x u v w).trans (curvatureTrilinearMap_apply D' x u v w).symm)
  simp only [actualDifferenceEnergyDensity, sub_self, Proofs.M03.connection_difference_eq_zero,
    hR, map_zero, PiLp.zero_apply, sq, zero_mul, Finset.sum_const_zero, add_zero]




theorem canonicalDifferenceEnergy_eq_zero_of_metric_eq
    {n dH dA dS : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) (φ : V n → ℝ) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J') (p : U) (t : ℝ),
      F.metric t = F'.metric t → canonicalDifferenceEnergy U hU qH qA qS φ F F' p t = 0 := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let : MeasurableSpace (V n) := borel _
  let : BorelSpace (V n) := ⟨rfl⟩
  intro J J' F F' p t h
  change (∫ x : V n, φ x ^ 2 * canonicalDifferenceDensity U hU qH qA qS F F' p t x) = 0
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall (fun x => by
    change φ x ^ 2 * actualDifferenceEnergyDensity qH qA qS
      (F.connection t) (F'.connection t) ((extChartAt (𝓡 n) p).symm x) = 0
    rw [actualDifferenceEnergyDensity_eq_zero_of_metric_eq
      qH qA qS h (F.connection t) (F'.connection t), mul_zero])

end PoincareConjecture.M34
