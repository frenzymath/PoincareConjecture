import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.CorePullbackBounds
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndPullbackBounds
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.IndexedSupportIntegral
import PoincareConjecture.Proofs.M34.Standard.UniformFamilyEnergyBounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

open DifferenceEnergy




theorem partialFlows_capDifferenceEnergy_bounds (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F F' : PartialStandardCapFlow g0) (e : StandardCylindricalEnd g0.metric)
    {dH dA dS : ℕ} (qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {S B : ℝ} (hS : 0 < S) (hSF : S ≤ F.lifetime) (hSF' : S ≤ F'.lifetime)
    (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B)
    (hfull' : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F'.flow.connection t).curvatureTensorNorm x ≤ B)
    (p : endReferenceRegion e) :
    let E := capDifferenceEnergy e qH qA qS F.flow F'.flow p
    let D := capDifferenceSupportIntegral e qH qA qS F.flow F'.flow p
    ∃ M C : ℝ, 0 ≤ M ∧ 0 ≤ C ∧
      (∀ i t, t ∈ Ico 0 S → E i t ≤ M) ∧
      (∀ i t, t ∈ Ico 0 S → t ∈ interior (Ico 0 F.lifetime ∩ Ico 0 F'.lifetime) →
        deriv (E i) t ≤ C * D i t) := by
  let := (isOpen_univ : IsOpen (univ : Set (V 3))).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (isOpen_univ : IsOpen (univ : Set (V 3))).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  let : MeasurableSpace StandardCapSpace := borel _
  let : BorelSpace StandardCapSpace := ⟨rfl⟩
  intro E D
  obtain ⟨ac, Mc, hac, _hMc, hc⟩ := partialFlow_corePullback_bounds P E0 F
    hS hSF hB hfull (energyCutoffs_hasCompactSupport e).2 3
  obtain ⟨ac', Mc', hac', _hMc', hc'⟩ := partialFlow_corePullback_bounds P E0 F'
    hS hSF' hB hfull' (energyCutoffs_hasCompactSupport e).2 3
  obtain ⟨ae, Me, hae, _hMe, he⟩ := partialFlow_endPullback_bounds P E0 F e
    hS hSF hB hfull (energyCutoffs_hasCompactSupport e).1 3
  obtain ⟨ae', Me', hae', _hMe', he'⟩ := partialFlow_endPullback_bounds P E0 F' e
    hS hSF' hB hfull' (energyCutoffs_hasCompactSupport e).1 3
  let pc : (univ : Set (V 3)) := ⟨0, mem_univ _⟩
  obtain ⟨Bc, Lc, hBc, hLc, hfc⟩ := exists_uniformFamily_energy_bounds univ isOpen_univ
    qH qA qS ((energyCutoffs_contDiff e).2.of_le (by simp))
    (energyCutoffs_hasCompactSupport e).2 (subset_univ _) hac hac' Mc Mc'
  obtain ⟨hvc, hrc⟩ := hfc (K := Ico 0 S)
    (fun _ : Unit => canonicalCoreFlow F.flow) (fun _ : Unit => canonicalCoreFlow F'.flow) pc
    (fun _ t ht x hx => hc t ht pc x hx) (fun _ t ht x hx => hc' t ht pc x hx)
  obtain ⟨Be, Le, hBe, hLe, hfe⟩ := exists_uniformFamily_energy_bounds
    (endReferenceRegion e) (endReferenceRegion_isOpen e) qH qA qS
    ((energyCutoffs_contDiff e).1.of_le (by simp)) (energyCutoffs_hasCompactSupport e).1
    (endEnergyCutoff_tsupport_subset_region e) hae hae' Me Me'
  have hj (j : ℕ) : -3 < (j : ℝ) := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  obtain ⟨hve, hre⟩ := hfe (K := Ico 0 S)
    (fun j : ℕ => endPullbackFlow e F.flow j (hj j))
    (fun j : ℕ => endPullbackFlow e F'.flow j (hj j)) p
    (fun j t ht x hx => he j (hj j) t ht p x hx (endEnergyCutoff_tsupport_subset_region e hx))
    (fun j t ht x hx => he' j (hj j) t ht p x hx (endEnergyCutoff_tsupport_subset_region e hx))
  have htJ (t) (ht : t ∈ Ico 0 S) : t ∈ Ico 0 F.lifetime ∩ Ico 0 F'.lifetime :=
    ⟨⟨ht.1, ht.2.trans_le hSF⟩, ⟨ht.1, ht.2.trans_le hSF'⟩⟩
  refine ⟨max Bc Be, max Lc Le, hBc.trans (le_max_left _ _),
    hLc.trans (le_max_left _ _), ?_, ?_⟩
  · intro i t ht
    cases i with
    | zero => exact (hvc () t ht (htJ t ht)).trans (le_max_left _ _)
    | succ j => exact (hve j t ht (htJ t ht)).trans (le_max_right _ _)
  · intro i t ht hi
    have hD : 0 ≤ D i t := capDifferenceSupportIntegral_nonneg e qH qA qS F.flow F'.flow p i t
    cases i with
    | zero =>
      have hr : deriv (E 0) t ≤ Lc * D 0 t := by
        simpa only [E, D, capDifferenceEnergy, capDifferenceSupportIntegral,
          canonicalCoreFlow_chart_density] using hrc () t ht hi
      exact hr.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hD)
    | succ j =>
      exact (hre j t ht hi).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hD)

end PoincareConjecture.M34
