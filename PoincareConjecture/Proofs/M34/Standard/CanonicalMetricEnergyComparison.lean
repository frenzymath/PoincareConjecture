import PoincareConjecture.Proofs.M34.Standard.CanonicalDifferenceEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

theorem canonicalDifferenceEnergy_metric_part_le
    {n dH dA dS : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {φ : V n → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    letI : MeasurableSpace (V n) := borel _
    letI : BorelSpace (V n) := ⟨rfl⟩
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J') (p : U)
      {t : ℝ}, t ∈ J ∩ J' → ∀ H : V n → FH n,
      (∀ x : U, H x = (F.metric t).inner x - (F'.metric t).inner x) →
      (∑ i, ∫ x, (φ x * qH (H x) i) ^ 2) ≤
        canonicalDifferenceEnergy U hU qH qA qS φ F F' p t := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let : MeasurableSpace (V n) := borel _
  let : BorelSpace (V n) := ⟨rfl⟩
  intro J J' F F' p t ht H hH
  let r := (extChartAt (𝓡 n) p).symm
  let G : V n → FH n := fun x => (F.metric t).inner (r x) - (F'.metric t).inner (r x)
  let A : V n → FA n := fun x => CovariantDerivative.difference
    (F.connection t).connection (F'.connection t).connection (r x)
  let S : V n → FS n := fun x => curvatureTrilinearMap (F.connection t) (r x) -
    curvatureTrilinearMap (F'.connection t) (r x)
  let EA := ∑ i, ∫ x, (φ x * qA (A x) i) ^ 2
  let ES := ∑ i, ∫ x, (φ x * qS (S x) i) ^ 2
  have hsum : canonicalDifferenceEnergy U hU qH qA qS φ F F' p t =
      (∑ i, ∫ x, (φ x * qH (G x) i) ^ 2) + EA + ES :=
    canonicalDifferenceDensity_integral_eq U hU qH qA qS hφ hφc hφU F F' p ht
  have hmetric : (∑ i, ∫ x, (φ x * qH (H x) i) ^ 2) =
      ∑ i, ∫ x, (φ x * qH (G x) i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _hi
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    change (φ x * qH (H x) i) ^ 2 = (φ x * qH (G x) i) ^ 2
    by_cases hx : φ x = 0
    · simp only [hx, zero_mul]
    have hxU : x ∈ U := hφU (subset_tsupport φ hx)
    have heq : H x = G x := by
      rw [hH ⟨x, hxU⟩]
      dsimp only [G, r]
      rw [show (extChartAt (𝓡 n) p).symm x = ⟨x, hxU⟩ from
        canonicalOpen_chart_symm_apply hU p ⟨x, hxU⟩]
    rw [heq]
  have hEA : 0 ≤ EA := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hES : 0 ≤ ES := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  rw [hmetric, hsum]
  linarith only [hEA, hES]

end PoincareConjecture.M34
