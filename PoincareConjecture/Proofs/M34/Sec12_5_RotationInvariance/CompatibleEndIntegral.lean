import PoincareConjecture.Proofs.M03.CompactCoordinateChange
import PoincareConjecture.Proofs.M34.Mathlib.FiniteCoverIntegral
import PoincareConjecture.Proofs.M34.Standard.CanonicalDensityIntegral
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.CompatibleEndDensity
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndSlabCover











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy




theorem exists_compatibleEnd_integral_bound
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
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J0 J0' J1 J1' : Set ℝ}
      (F0 : RicciFlow 3 (endReferenceRegion e) J0)
      (F0' : RicciFlow 3 (endReferenceRegion e) J0')
      (F1 : RicciFlow 3 (endReferenceRegion e) J1)
      (F1' : RicciFlow 3 (endReferenceRegion e) J1')
      (p : endReferenceRegion e) {t : ℝ}, t ∈ J0 ∩ J0' → t ∈ J1 ∩ J1' →
      (∀ y ∈ endReferenceOverlap e r, ∀ u v : TangentSpace (𝓡 3) y,
        (F0.metric t).inner y u v = (F1.metric t).inner (endReferenceTransition e p r y)
          (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y u)
          (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y v)) →
      (∀ y ∈ endReferenceOverlap e r, ∀ u v : TangentSpace (𝓡 3) y,
        (F0'.metric t).inner y u v = (F1'.metric t).inner (endReferenceTransition e p r y)
          (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y u)
          (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y v)) →
      (∫ x in endAxialTranslation e (-r) '' Q,
        canonicalDifferenceDensity (endReferenceRegion e) (endReferenceRegion_isOpen e)
          qH qA qS F0 F0' p t x) ≤
        C * ∫ x, endEnergyCutoff e x ^ 2 *
          canonicalDifferenceDensity (endReferenceRegion e) (endReferenceRegion_isOpen e)
            qH qA qS F1 F1' p t x := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  let : MeasurableSpace StandardCapSpace := borel _
  let : BorelSpace StandardCapSpace := ⟨rfl⟩
  have hneg : -3 < -r := by rcases hr with rfl | rfl | rfl <;> norm_num
  have hT := (endReferenceTranslation_contMDiffOn e hneg).contDiffOn
  obtain ⟨D, hD, hpoint⟩ := exists_compatibleEnd_density_bound e qH qA qS hK hKU
  obtain ⟨B, hB, hchange⟩ := Proofs.M03.exists_compact_coordinate_change_integral_bound
    (endReferenceRegion_isOpen e) (hT.of_le (by decide))
    (endAxialTranslation_injOn_reference e (-r) hneg) hQ (hQK.trans hKU)
  refine ⟨B * D, mul_nonneg hB hD, ?_⟩
  intro J0 J0' J1 J1' F0 F0' F1 F1' p t ht0 ht1 hm0 hm1
  let dj := canonicalDifferenceDensity (endReferenceRegion e) (endReferenceRegion_isOpen e)
    qH qA qS F0 F0' p t
  let dk := canonicalDifferenceDensity (endReferenceRegion e) (endReferenceRegion_isOpen e)
    qH qA qS F1 F1' p t
  have hjc : ContinuousOn dj (endReferenceRegion e) :=
    canonicalDifferenceDensity_continuousOn_slice _ _ qH qA qS F0 F0' p ht0
  have hkc : ContinuousOn dk (endReferenceRegion e) :=
    canonicalDifferenceDensity_continuousOn_slice _ _ qH qA qS F1 F1' p ht1
  have hj0 (x) : 0 ≤ dj x := canonicalDifferenceDensity_nonneg _ _ qH qA qS F0 F0' p t x
  have hk0 (x) : 0 ≤ dk x := canonicalDifferenceDensity_nonneg _ _ qH qA qS F1 F1' p t x
  have hjQ : IntegrableOn (fun x => dj (endAxialTranslation e (-r) x)) Q :=
    ContinuousOn.integrableOn_compact hQ (hjc.comp (hT.continuousOn.mono (hQK.trans hKU))
      (fun x hx => hKU (himage (mem_image_of_mem _ hx))))
  have hkQ : IntegrableOn dk Q := ContinuousOn.integrableOn_compact hQ (hkc.mono (hQK.trans hKU))
  have hcompare (y : StandardCapSpace) (hy : y ∈ Q) :
      dj (endAxialTranslation e (-r) y) ≤ D * dk y := by
    have hxK := himage (mem_image_of_mem (endAxialTranslation e (-r)) hy)
    let x : endReferenceRegion e := ⟨endAxialTranslation e (-r) y, hKU hxK⟩
    have hinv : endAxialTranslation e r x = y := by
      rw [show (x : StandardCapSpace) = endAxialTranslation e (-r) y from rfl,
        endAxialTranslation_comp_reference e (-r) hneg r (hKU (hQK hy)), neg_add_cancel,
        endAxialTranslation_zero_reference e (hKU (hQK hy))]
    have hshift : endAxialTranslation e r x ∈ K := by rw [hinv]; exact hQK hy
    have hh := hpoint _ _ _ _ (F0.connection t) (F0'.connection t)
      (F1.connection t) (F1'.connection t) p r hr hm0 hm1 x hxK hshift
    have heq : endReferenceTransition e p r x = (extChartAt (𝓡 3) p).symm y := by
      change (extChartAt (𝓡 3) p).symm (endAxialTranslation e r x) = _
      rw [hinv]
    rw [heq] at hh
    change canonicalDifferenceDensity _ _ qH qA qS F0 F0' p t (x : StandardCapSpace) ≤ D * dk y
    rw [canonicalDifferenceDensity_coe]
    exact hh
  have hki : Integrable (fun x => endEnergyCutoff e x ^ 2 * dk x) :=
    canonicalDifferenceDensity_integrable_cutoff _ _ qH qA qS
      (energyCutoffs_contDiff e).1.continuous (energyCutoffs_hasCompactSupport e).1
      (endEnergyCutoff_tsupport_subset_region e) F1 F1' p ht1
  have hplateauI := setIntegral_le_cutoff_sq_integral hQ.measurableSet hki hk0 hplateau
  change (∫ x in endAxialTranslation e (-r) '' Q, dj x) ≤
    (B * D) * ∫ x, endEnergyCutoff e x ^ 2 * dk x
  calc
    _ ≤ B * ∫ y in Q, dj (endAxialTranslation e (-r) y) :=
      hchange dj (hjc.mono (himage.trans hKU)) (fun y _ => hj0 y)
    _ ≤ B * ∫ y in Q, D * dk y := mul_le_mul_of_nonneg_left
      (setIntegral_mono_on hjQ (hkQ.const_mul D) hQ.measurableSet hcompare) hB
    _ = (B * D) * ∫ y in Q, dk y := by rw [integral_const_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hplateauI (mul_nonneg hB hD)

end PoincareConjecture.M34
