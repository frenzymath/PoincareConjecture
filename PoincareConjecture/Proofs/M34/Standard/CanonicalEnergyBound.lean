import PoincareConjecture.Proofs.M34.Standard.CanonicalDensityBound
import PoincareConjecture.Proofs.M34.Standard.CanonicalDifferenceEnergy











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy




theorem exists_canonicalDifferenceEnergy_bound
    {n dH dA dS : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {φ : V n → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) {a : ℝ} (ha : 0 < a) (M : ℝ) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {J J' : Set ℝ}
      (F : RicciFlow n U J) (F' : RicciFlow n U J') (p : U) {t : ℝ}, t ∈ J ∩ J' →
      let B0 := (F.metric t).pullbackCoefficients (extChartAt (𝓡 n) p).symm
      let B1 := (F'.metric t).pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (∀ x ∈ tsupport φ, ∀ j ≤ 3, ‖iteratedFDeriv ℝ j B0 x‖ ≤ M) →
      (∀ x ∈ tsupport φ, ∀ j ≤ 3, ‖iteratedFDeriv ℝ j B1 x‖ ≤ M) →
      (∀ x ∈ tsupport φ, ∀ v, a * ‖v‖ ^ 2 ≤ B0 x v v) →
      (∀ x ∈ tsupport φ, ∀ v, a * ‖v‖ ^ 2 ≤ B1 x v v) →
      canonicalDifferenceEnergy U hU qH qA qS φ F F' p t ≤ B := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let : MeasurableSpace (V n) := borel _
  let : BorelSpace (V n) := ⟨rfl⟩
  obtain ⟨D, hD, hbound⟩ := exists_canonicalDomain_differenceDensity_bound qH qA qS ha M
  have hwc : HasCompactSupport (fun x => φ x ^ 2) :=
    hφc.comp_left (g := fun r : ℝ => r ^ 2) (by simp)
  have hwi : Integrable (fun x : V n => φ x ^ 2) (volume : Measure (V n)) :=
    (hφ.pow 2).integrable_of_hasCompactSupport hwc
  refine ⟨(∫ x : V n, φ x ^ 2) * D, mul_nonneg (integral_nonneg (fun x => sq_nonneg _)) hD, ?_⟩
  intro J J' F F' p t ht B0 B1 hj0 hj1 he0 he1
  have hi := canonicalDifferenceDensity_integrable_cutoff U hU qH qA qS
    hφ hφc hφU F F' p ht
  have hp (x : V n) : φ x ^ 2 * canonicalDifferenceDensity U hU qH qA qS F F' p t x ≤
      φ x ^ 2 * D := by
    by_cases hx : x ∈ tsupport φ
    · exact mul_le_mul_of_nonneg_left
        (hbound U hU inferInstance (F.metric t) (F.connection t) (F'.metric t)
          (F'.connection t) p x (hφU hx) (hj0 x hx) (hj1 x hx) (he0 x hx) (he1 x hx))
        (sq_nonneg _)
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_pow (by decide : 2 ≠ 0),
        zero_mul, le_refl]
  exact (integral_mono hi (hwi.mul_const D) hp).trans_eq (integral_mul_const _ _)

end PoincareConjecture.M34
