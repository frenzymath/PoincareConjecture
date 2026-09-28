import PoincareConjecture.Proofs.M34.Standard.CanonicalDifferenceEnergy
import PoincareConjecture.Proofs.M34.Standard.ActualDifferenceEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

theorem exists_canonicalDifferenceEnergy_rate_bound
    {n dH dA dS : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {φ : V n → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) {a : ℝ} (ha : 0 < a) (M : ℝ) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    letI : MeasurableSpace (V n) := borel _
    letI : BorelSpace (V n) := ⟨rfl⟩
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J J' : Set ℝ}
      (F : RicciFlow n U J) (F' : RicciFlow n U J') (p : U) {t : ℝ},
      t ∈ interior (J ∩ J') →
      let B0 := (F.metric t).pullbackCoefficients (extChartAt (𝓡 n) p).symm
      let B1 := (F'.metric t).pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (∀ x ∈ tsupport φ, ∀ j ≤ 3, ‖iteratedFDeriv ℝ j B0 x‖ ≤ M) →
      (∀ x ∈ tsupport φ, ∀ j ≤ 3, ‖iteratedFDeriv ℝ j B1 x‖ ≤ M) →
      (∀ x ∈ tsupport φ, ∀ v, a * ‖v‖ ^ 2 ≤ B0 x v v) →
      (∀ x ∈ tsupport φ, ∀ v, a * ‖v‖ ^ 2 ≤ B1 x v v) →
      deriv (canonicalDifferenceEnergy U hU qH qA qS φ F F' p) t ≤
        C * ∫ x in tsupport φ, canonicalDifferenceDensity U hU qH qA qS F F' p t x := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let : MeasurableSpace (V n) := borel _
  let : BorelSpace (V n) := ⟨rfl⟩
  obtain ⟨lambda, C, hlambda, hC, hbound⟩ :=
    exists_uniform_actual_difference_energy_bound U hU qH qA qS hφ hφc hφU ha M
  refine ⟨C, hC, ?_⟩
  intro J J' F F' p t ht B0 B1 hj0 hj1 he0 he1
  let r := (extChartAt (𝓡 n) p).symm
  let H : ℝ × V n → FH n := fun z => (F.metric z.1).inner (r z.2) -
    (F'.metric z.1).inner (r z.2)
  let A : ℝ × V n → FA n := fun z => CovariantDerivative.difference
    (F.connection z.1).connection (F'.connection z.1).connection (r z.2)
  let S : ℝ × V n → FS n := fun z => curvatureTrilinearMap (F.connection z.1) (r z.2) -
    curvatureTrilinearMap (F'.connection z.1) (r z.2)
  let E : ℝ → ℝ := fun s => (∑ i, ∫ x, (φ x * qH (H (s, x)) i) ^ 2) +
    (∑ i, ∫ x, (φ x * qA (A (s, x)) i) ^ 2) +
    (∑ i, ∫ x, (φ x * qS (S (s, x)) i) ^ 2)
  have heq : canonicalDifferenceEnergy U hU qH qA qS φ F F' p =ᶠ[𝓝 t] E := by
    filter_upwards [mem_interior_iff_mem_nhds.mp ht] with s hs
    exact canonicalDifferenceDensity_integral_eq U hU qH qA qS
      hφ.continuous hφc hφU F F' p hs
  have hr := hbound F F' (fun s x => curvatureTrilinearMap (F.connection s) x)
    (fun s x => curvatureTrilinearMap (F'.connection s) x)
    (fun s x u v w => curvatureTrilinearMap_apply (F.connection s) x u v w)
    (fun s x u v w => curvatureTrilinearMap_apply (F'.connection s) x u v w)
    p t ht hj0 hj1 he0 he1
  rw [heq.deriv_eq]
  apply hr.trans
  apply sub_le_self
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun _ _ => integral_nonneg (fun x =>
    mul_nonneg (sq_nonneg (φ x)) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))))

end PoincareConjecture.M34
