import PoincareConjecture.Proofs.M34.Standard.CanonicalDifferenceEnergy
import PoincareConjecture.Proofs.M34.Mathlib.FiniteCoordinateEnergyZero

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

theorem canonicalDifferenceEnergy_metric_eq_of_zero
    {n dH dA dS : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {φ : V n → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J') (p : U)
      {t : ℝ}, t ∈ J ∩ J' → canonicalDifferenceEnergy U hU qH qA qS φ F F' p t = 0 →
      ∀ x : U, φ x ≠ 0 → (F.metric t).inner x = (F'.metric t).inner x := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let : MeasurableSpace (V n) := borel _
  let : BorelSpace (V n) := ⟨rfl⟩
  intro J J' F F' p t ht hzero x hx
  let r := (extChartAt (𝓡 n) p).symm
  let H : V n → FH n := fun y => (F.metric t).inner (r y) - (F'.metric t).inner (r y)
  let A : V n → FA n := fun y => CovariantDerivative.difference
    (F.connection t).connection (F'.connection t).connection (r y)
  let S : V n → FS n := fun y => curvatureTrilinearMap (F.connection t) (r y) -
    curvatureTrilinearMap (F'.connection t) (r y)
  let EH := ∑ i, ∫ y, (φ y * qH (H y) i) ^ 2
  let EA := ∑ i, ∫ y, (φ y * qA (A y) i) ^ 2
  let ES := ∑ i, ∫ y, (φ y * qS (S y) i) ^ 2
  have hsum : canonicalDifferenceEnergy U hU qH qA qS φ F F' p t = EH + EA + ES :=
    canonicalDifferenceDensity_integral_eq U hU qH qA qS hφ hφc hφU F F' p ht
  have hEH : 0 ≤ EH := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hEA : 0 ≤ EA := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hES : 0 ≤ ES := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hHzero : EH = 0 := by linarith only [hsum, hzero, hEH, hEA, hES]
  obtain ⟨hsH, _hsA, _hsS⟩ := canonicalDomain_contDiffOn_difference_coordinates U hU
    qH qA qS F F' (fun s y => curvatureTrilinearMap (F.connection s) y)
    (fun s y => curvatureTrilinearMap (F'.connection s) y)
    (fun s y u v w => curvatureTrilinearMap_apply (F.connection s) y u v w)
    (fun s y u v w => curvatureTrilinearMap_apply (F'.connection s) y u v w) p
  have hcH : ContinuousOn (fun y => qH (H y)) U := by
    intro y hy
    exact (hsH.continuousOn (t, y) ⟨ht, hy⟩).comp
      (continuous_const.prodMk continuous_id).continuousWithinAt (fun _ hz => ⟨ht, hz⟩)
  have hv := (finite_coordinate_energy_eq_zero_iff hU hcH hφ hφc hφU).mp hHzero x hx
  have hH : H x = 0 := qH.injective (hv.trans (map_zero qH).symm)
  have hi := sub_eq_zero.mp hH
  change (F.metric t).inner (r x) = (F'.metric t).inner (r x) at hi
  dsimp only [r] at hi
  rw [show (extChartAt (𝓡 n) p).symm (x : V n) = x from
    canonicalOpen_chart_symm_apply hU p x] at hi
  exact hi

end PoincareConjecture.M34
