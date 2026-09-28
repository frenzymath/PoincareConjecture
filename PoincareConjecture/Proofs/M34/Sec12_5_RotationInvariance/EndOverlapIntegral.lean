import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.CompatibleEndIntegral
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndDensityComparison











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy




theorem exists_endOverlap_integral_bound
    {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)
    {dH dA dS : ℕ} (qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {K Q : Set StandardCapSpace} (hK : IsCompact K) (hKU : K ⊆ endReferenceRegion e)
    (hQ : IsCompact Q) (hQK : Q ⊆ K) {r : ℝ} (hr : r = -1 ∨ r = 0 ∨ r = 1)
    (himage : endAxialTranslation e (-r) '' Q ⊆ K)
    (hplateau : ∀ x ∈ Q, endEnergyCutoff e x = 1) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    letI : MeasurableSpace StandardCapSpace := borel _
    letI : BorelSpace StandardCapSpace := ⟨rfl⟩
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J J' : Set ℝ}
      (F : RicciFlow 3 StandardCapSpace J) (F' : RicciFlow 3 StandardCapSpace J')
      (p : endReferenceRegion e) (s : ℝ) (hs : -3 < s) (hrs : -3 < r + s)
      {t : ℝ}, t ∈ J ∩ J' →
      (∫ x in endAxialTranslation e (-r) '' Q,
        canonicalDifferenceDensity (endReferenceRegion e) (endReferenceRegion_isOpen e)
          qH qA qS (endPullbackFlow e F (r + s) hrs) (endPullbackFlow e F' (r + s) hrs) p t x) ≤
        C * ∫ x, endEnergyCutoff e x ^ 2 *
          canonicalDifferenceDensity (endReferenceRegion e) (endReferenceRegion_isOpen e)
            qH qA qS (endPullbackFlow e F s hs) (endPullbackFlow e F' s hs) p t x := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  let : MeasurableSpace StandardCapSpace := borel _
  let : BorelSpace StandardCapSpace := ⟨rfl⟩
  obtain ⟨C, hC, hcompare⟩ := exists_compatibleEnd_integral_bound e qH qA qS
    hK hKU hQ hQK hr himage hplateau
  refine ⟨C, hC, ?_⟩
  intro J J' F F' p s hs hrs t ht
  have hrpos : -3 < r := by rcases hr with rfl | rfl | rfl <;> norm_num
  exact hcompare (endPullbackFlow e F (r + s) hrs) (endPullbackFlow e F' (r + s) hrs)
    (endPullbackFlow e F s hs) (endPullbackFlow e F' s hs) p ht ht
    (endReferenceTransition_metric e F p r hrpos s hs hrs t)
    (endReferenceTransition_metric e F' p r hrpos s hs hrs t)

end PoincareConjecture.M34
