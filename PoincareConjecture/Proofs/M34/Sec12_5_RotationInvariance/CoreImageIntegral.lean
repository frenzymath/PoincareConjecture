import PoincareConjecture.Proofs.M03.CompactCoordinateChange
import PoincareConjecture.Proofs.M34.Mathlib.FiniteCoverIntegral
import PoincareConjecture.Proofs.M34.Standard.CanonicalCoreFlow
import PoincareConjecture.Proofs.M34.Standard.CanonicalDensityIntegral
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndOriginalDensity
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndCompactSlabs










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy




theorem exists_coreImage_integral_bound
    {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)
    {dH dA dS : ℕ} (qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    (s : ℝ) (hs : -3 < s) {Q : Set StandardCapSpace} (hQ : IsCompact Q)
    (hQU : Q ⊆ endReferenceRegion e) (hplateau : ∀ x ∈ Q, endEnergyCutoff e x = 1) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    letI : MeasurableSpace StandardCapSpace := borel _
    letI : BorelSpace StandardCapSpace := ⟨rfl⟩
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J J' : Set ℝ}
      (F : RicciFlow 3 StandardCapSpace J) (F' : RicciFlow 3 StandardCapSpace J')
      (p : endReferenceRegion e) {t : ℝ}, t ∈ J ∩ J' →
      (∫ x in endAxialTranslation e s '' Q,
        actualDifferenceEnergyDensity qH qA qS (F.connection t) (F'.connection t) x) ≤
        C * ∫ x, endEnergyCutoff e x ^ 2 *
          canonicalDifferenceDensity (endReferenceRegion e) (endReferenceRegion_isOpen e)
            qH qA qS (endPullbackFlow e F s hs) (endPullbackFlow e F' s hs) p t x := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  let : MeasurableSpace StandardCapSpace := borel _
  let : BorelSpace StandardCapSpace := ⟨rfl⟩
  obtain ⟨D, hD, hcompare⟩ := exists_endOriginal_density_bounds e qH qA qS s hs hQ hQU
  have hT := (endReferenceTranslation_contMDiffOn e hs).contDiffOn
  obtain ⟨B, hB, hchange⟩ := Proofs.M03.exists_compact_coordinate_change_integral_bound
    (endReferenceRegion_isOpen e) (hT.of_le (by decide))
    (endAxialTranslation_injOn_reference e s hs) hQ hQU
  refine ⟨B * D, mul_nonneg hB hD, ?_⟩
  intro J J' F F' p t ht
  let dc := actualDifferenceEnergyDensity qH qA qS (F.connection t) (F'.connection t)
  let de := canonicalDifferenceDensity (endReferenceRegion e) (endReferenceRegion_isOpen e)
    qH qA qS (endPullbackFlow e F s hs) (endPullbackFlow e F' s hs) p t
  have hcc : Continuous dc := actualDifferenceEnergyDensity_continuous_euclidean qH qA qS F F' ht
  have hec : ContinuousOn de (endReferenceRegion e) :=
    canonicalDifferenceDensity_continuousOn_slice _ _ qH qA qS _ _ p ht
  have hc0 (x) : 0 ≤ dc x := actualDifferenceEnergyDensity_nonneg qH qA qS _ _ x
  have he0 (x) : 0 ≤ de x := canonicalDifferenceDensity_nonneg _ _ qH qA qS _ _ p t x
  have hci : IntegrableOn (fun x => dc (endAxialTranslation e s x)) Q :=
    ContinuousOn.integrableOn_compact hQ (hcc.comp_continuousOn (hT.continuousOn.mono hQU))
  have hei : IntegrableOn de Q := ContinuousOn.integrableOn_compact hQ (hec.mono hQU)
  have hweighted : Integrable (fun x => endEnergyCutoff e x ^ 2 * de x) :=
    canonicalDifferenceDensity_integrable_cutoff _ _ qH qA qS
      (energyCutoffs_contDiff e).1.continuous (energyCutoffs_hasCompactSupport e).1
      (endEnergyCutoff_tsupport_subset_region e) _ _ p ht
  have hlast := setIntegral_le_cutoff_sq_integral hQ.measurableSet hweighted he0 hplateau
  change (∫ x in endAxialTranslation e s '' Q, dc x) ≤
    (B * D) * ∫ x, endEnergyCutoff e x ^ 2 * de x
  calc
    _ ≤ B * ∫ x in Q, dc (endAxialTranslation e s x) :=
      hchange dc hcc.continuousOn (fun x _ => hc0 x)
    _ ≤ B * ∫ x in Q, D * de x := mul_le_mul_of_nonneg_left
      (setIntegral_mono_on hci (hei.const_mul D) hQ.measurableSet
        (fun x hx => (hcompare F F' p t x hx).2)) hB
    _ = (B * D) * ∫ x in Q, de x := by rw [integral_const_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlast (mul_nonneg hB hD)

end PoincareConjecture.M34
