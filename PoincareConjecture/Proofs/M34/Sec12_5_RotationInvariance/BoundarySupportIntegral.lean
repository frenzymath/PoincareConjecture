import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.CoreBandIntegral











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy




theorem exists_boundarySupport_integral_bound
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
      let dc := actualDifferenceEnergyDensity qH qA qS (F.connection t) (F'.connection t)
      let rho := fun j : ℕ => canonicalDifferenceDensity
        (endReferenceRegion e) (endReferenceRegion_isOpen e) qH qA qS
        (endPullbackFlow e F j (by have := Nat.cast_nonneg (α := ℝ) j; linarith))
        (endPullbackFlow e F' j (by have := Nat.cast_nonneg (α := ℝ) j; linarith)) p t
      let B := (∫ x, coreEnergyCutoff e x ^ 2 * dc x) +
        (∫ x, endEnergyCutoff e x ^ 2 * rho 0 x) +
        (∫ x, endEnergyCutoff e x ^ 2 * rho 1 x)
      (∫ x in tsupport (coreEnergyCutoff e), dc x) ≤ C * B ∧
        (∫ x in tsupport (endEnergyCutoff e), rho 0 x) ≤ C * B := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  let : MeasurableSpace StandardCapSpace := borel _
  let : BorelSpace StandardCapSpace := ⟨rfl⟩
  obtain ⟨Cb, hCb, hband⟩ := exists_coreBand_integral_bound e qH qA qS
  obtain ⟨D, hD, hcompare⟩ := exists_endOriginal_density_bounds e qH qA qS 0 (by norm_num)
    (energyCutoffs_hasCompactSupport e).1 (endEnergyCutoff_tsupport_subset_region e)
  let C := max Cb (D * Cb)
  refine ⟨C, hCb.trans (le_max_left _ _), ?_⟩
  intro J J' F F' p t ht dc rho B
  have hc : Continuous dc := actualDifferenceEnergyDensity_continuous_euclidean qH qA qS F F' ht
  have hd0 (x) : 0 ≤ dc x := actualDifferenceEnergyDensity_nonneg qH qA qS _ _ x
  have hr0 (j : ℕ) (x : StandardCapSpace) : 0 ≤ rho j x :=
    canonicalDifferenceDensity_nonneg _ _ qH qA qS _ _ p t x
  have hB : 0 ≤ B := add_nonneg
    (add_nonneg (integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hd0 x)))
      (integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hr0 0 x))))
    (integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hr0 1 x)))
  have hci : IntegrableOn dc {x | endExhaustion e x ≤ 6} :=
    ContinuousOn.integrableOn_compact (endExhaustion_sublevel_isCompact e 6) hc.continuousOn
  have hb : (∫ x in {x | endExhaustion e x ≤ 6}, dc x) ≤ Cb * B := hband F F' p ht
  have hendSub : tsupport (endEnergyCutoff e) ⊆ {x | endExhaustion e x ≤ 6} := by
    intro x hx
    have hh := (endEnergyCutoff_tsupport e hx).2
    change endExhaustion e x ≤ 6
    linarith
  constructor
  · exact ((setIntegral_mono_set hci (Filter.Eventually.of_forall hd0)
      (Filter.Eventually.of_forall (coreEnergyCutoff_tsupport e))).trans hb).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hB)
  · have hec : ContinuousOn (rho 0) (endReferenceRegion e) :=
      canonicalDifferenceDensity_continuousOn_slice _ _ qH qA qS _ _ p ht
    have hei : IntegrableOn (rho 0) (tsupport (endEnergyCutoff e)) :=
      ContinuousOn.integrableOn_compact (energyCutoffs_hasCompactSupport e).1
        (hec.mono (endEnergyCutoff_tsupport_subset_region e))
    have hdi : IntegrableOn dc (tsupport (endEnergyCutoff e)) :=
      ContinuousOn.integrableOn_compact (energyCutoffs_hasCompactSupport e).1 hc.continuousOn
    have hpoint (x) (hx : x ∈ tsupport (endEnergyCutoff e)) : rho 0 x ≤ D * dc x := by
      have hh := (hcompare F F' p t x hx).1
      simpa only [rho, Nat.cast_zero, endAxialTranslation_zero_reference e
        (endEnergyCutoff_tsupport_subset_region e hx)] using hh
    calc
      _ ≤ ∫ x in tsupport (endEnergyCutoff e), D * dc x :=
        setIntegral_mono_on hei (hdi.const_mul D) (isClosed_tsupport _).measurableSet hpoint
      _ = D * ∫ x in tsupport (endEnergyCutoff e), dc x := integral_const_mul _ _
      _ ≤ D * ∫ x in {x | endExhaustion e x ≤ 6}, dc x :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_set hci
          (Filter.Eventually.of_forall hd0) (Filter.Eventually.of_forall hendSub)) hD
      _ ≤ D * (Cb * B) := mul_le_mul_of_nonneg_left hb hD
      _ = (D * Cb) * B := by ring
      _ ≤ C * B := mul_le_mul_of_nonneg_right (le_max_right _ _) hB

end PoincareConjecture.M34
