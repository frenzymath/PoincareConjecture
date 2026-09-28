import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndOverlapIntegral
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.CompatibleEndNeighbors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

theorem exists_endNeighbor_integral_bound
    {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)
    {dH dA dS : ℕ} (qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    letI : MeasurableSpace StandardCapSpace := borel _
    letI : BorelSpace StandardCapSpace := ⟨rfl⟩
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J J' : Set ℝ}
      (F : RicciFlow 3 StandardCapSpace J) (F' : RicciFlow 3 StandardCapSpace J')
      (p : endReferenceRegion e) {t : ℝ}, t ∈ J ∩ J' →
      let rho := fun j : ℕ => canonicalDifferenceDensity
        (endReferenceRegion e) (endReferenceRegion_isOpen e) qH qA qS
        (endPullbackFlow e F j (by have := Nat.cast_nonneg (α := ℝ) j; linarith))
        (endPullbackFlow e F' j (by have := Nat.cast_nonneg (α := ℝ) j; linarith)) p t
      ∀ j : ℕ, (∫ x in tsupport (endEnergyCutoff e), rho (j + 1) x) ≤
        C * ((∫ x, endEnergyCutoff e x ^ 2 * rho j x) +
          (∫ x, endEnergyCutoff e x ^ 2 * rho (j + 1) x) +
          (∫ x, endEnergyCutoff e x ^ 2 * rho (j + 2) x)) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  let : MeasurableSpace StandardCapSpace := borel _
  let : BorelSpace StandardCapSpace := ⟨rfl⟩
  obtain ⟨C, hC, hcompare⟩ := exists_compatibleEnd_neighbor_bound e qH qA qS
  refine ⟨C, hC, ?_⟩
  intro J J' F F' p t ht
  have hj (j : ℕ) : -3 < (j : ℝ) := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  apply hcompare (fun j => endPullbackFlow e F j (hj j))
    (fun j => endPullbackFlow e F' j (hj j)) p ht
  · intro i j r hr hij x hx u v
    have hrpos : -3 < r := by rcases hr with rfl | rfl | rfl <;> norm_num
    have hrs : -3 < r + (j : ℝ) := by rw [← hij]; exact hj i
    simpa only [← hij] using endReferenceTransition_metric e F p r hrpos j (hj j) hrs t x hx u v
  · intro i j r hr hij x hx u v
    have hrpos : -3 < r := by rcases hr with rfl | rfl | rfl <;> norm_num
    have hrs : -3 < r + (j : ℝ) := by rw [← hij]; exact hj i
    simpa only [← hij] using endReferenceTransition_metric e F' p r hrpos j (hj j) hrs t x hx u v

end PoincareConjecture.M34
