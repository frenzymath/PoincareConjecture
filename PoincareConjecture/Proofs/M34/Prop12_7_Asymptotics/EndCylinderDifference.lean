import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderEnergyDecay
import PoincareConjecture.Proofs.M34.Standard.CanonicalMetricEnergyComparison












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy



noncomputable def endCylinderDifferenceCoefficients
    {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) (j : ℕ) (t : ℝ) : StandardCapSpace → FH 3 :=
  (F.metric t).pullbackCoefficients (endAxialTranslation e j) - endCylinderCoefficients e t




theorem endCylinderDifferenceCoefficients_contDiffOn
    {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) (j : ℕ) (t : ℝ) :
    ContDiffOn ℝ ∞ (endCylinderDifferenceCoefficients e F j t) (endReferenceRegion e) := by
  have hj : -3 < (j : ℝ) := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have hA : ContDiffOn ℝ ∞ ((F.metric t).pullbackCoefficients (endAxialTranslation e j))
      (endReferenceRegion e) := fun x hx => ((F.metric t).contDiffAt_pullbackCoefficients
    (((endReferenceTranslation_contMDiffOn e hj) x hx).contMDiffAt
      ((endReferenceRegion_isOpen e).mem_nhds hx))).contDiffWithinAt
  exact hA.sub (((endCylinderCoefficients_contDiff e).comp
    (contDiff_const.prodMk contDiff_id)).contDiffOn)




theorem partialFlow_endCylinderDifferenceCoefficients_bounds
    (P : RicciFlowCurvatureTheory.{0}) {g0 : StandardInitialMetric}
    (E0 : StandardCapEstimate g0) (F : PartialStandardCapFlow g0)
    (e : StandardCylindricalEnd g0.metric) {T : ℝ}
    (hT : T ∈ Ico 0 F.lifetime ∩ Ico 0 1)
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    ∃ M : ℝ, ∀ j t, t ∈ Icc 0 T → ∀ x ∈ K, x ∈ endReferenceRegion e →
      ‖iteratedFDeriv ℝ m (endCylinderDifferenceCoefficients e F.flow j t) x‖ ≤ M := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  obtain ⟨S, hTS, hSF⟩ := exists_between hT.1.2
  have hS : 0 < S := hT.1.1.trans_lt hTS
  obtain ⟨B0, _hB0, hb0⟩ := F.curvature_locally_bounded S hS.le hSF
  let B := max 1 B0
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hfull (s) (hs : s ∈ Ico 0 S) (x) : (F.flow.connection s).curvatureTensorNorm x ≤ B :=
    (le_abs_self _).trans ((hb0 s ⟨hs.1, hs.2.le⟩ x).trans (le_max_right _ _))
  obtain ⟨aA, MA, _haA, _hMA, hA⟩ := partialFlow_endPullback_bounds P E0 F e
    hS hSF.le hB hfull hK m
  obtain ⟨aB, MB, _haB, _hMB, hBmodel⟩ := endCylinderFlow_compact_bounds e hT.2.2 hK m
  refine ⟨MA + MB, ?_⟩
  intro j t ht x hx hxU
  have hj : -3 < (j : ℝ) := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  let p : endReferenceRegion e := ⟨x, hxU⟩
  have htI : t ∈ Ico 0 1 := ⟨ht.1, ht.2.trans_lt hT.2.2⟩
  have hjA := (hA j hj t ⟨ht.1, ht.2.trans_lt hTS⟩ p x hx hxU).1 m le_rfl
  have hjB := (hBmodel t ht p x hx hxU).1 m le_rfl
  rw [endPullbackFlow_iteratedFDeriv e F.flow j hj t p m x hxU] at hjA
  rw [endCylinderFlow_iteratedFDeriv e t htI p m x hxU] at hjB
  have hcA : ContDiffAt ℝ ∞ ((F.flow.metric t).pullbackCoefficients (endAxialTranslation e j)) x :=
    (F.flow.metric t).contDiffAt_pullbackCoefficients
      (((endReferenceTranslation_contMDiffOn e hj) x hxU).contMDiffAt
        ((endReferenceRegion_isOpen e).mem_nhds hxU))
  have hcB : ContDiffAt ℝ ∞ (endCylinderCoefficients e t) x :=
    ((endCylinderCoefficients_contDiff e).comp (contDiff_const.prodMk contDiff_id)).contDiffAt
  change ‖iteratedFDeriv ℝ m
    ((F.flow.metric t).pullbackCoefficients (endAxialTranslation e j) - endCylinderCoefficients e t)
      x‖ ≤ MA + MB
  rw [iteratedFDeriv_sub_apply (hcA.of_le (by exact_mod_cast le_top))
    (hcB.of_le (by exact_mod_cast le_top))]
  exact (norm_sub_le _ _).trans (add_le_add hjA hjB)




theorem endCylinderDifferenceCoefficients_energy_le
    {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)
    {dH dA dS : ℕ} (qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) (p : endReferenceRegion e)
    {t : ℝ} (ht : t ∈ J ∩ Ico 0 1) (j : ℕ) :
    letI : MeasurableSpace StandardCapSpace := borel _
    letI : BorelSpace StandardCapSpace := ⟨rfl⟩
    (∑ i, ∫ x, (endEnergyCutoff e x * qH (endCylinderDifferenceCoefficients e F j t x) i) ^ 2) ≤
      endCylinderDifferenceEnergy e qH qA qS F p j t := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  let : MeasurableSpace StandardCapSpace := borel _
  let : BorelSpace StandardCapSpace := ⟨rfl⟩
  have hj : -3 < (j : ℝ) := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  apply canonicalDifferenceEnergy_metric_part_le (endReferenceRegion e)
    (endReferenceRegion_isOpen e) qH qA qS
    (energyCutoffs_contDiff e).1.continuous (energyCutoffs_hasCompactSupport e).1
    (endEnergyCutoff_tsupport_subset_region e)
    (endPullbackFlow e F j hj) (endCylinderFlow e) p ht
  intro x
  rw [endPullbackFlow_inner e F j hj t x]
  ext u v
  change ((F.metric t).pullbackCoefficients (endAxialTranslation e j) x u v -
    endCylinderCoefficients e t x u v) =
      ((F.metric t).pullbackCoefficients (endAxialTranslation e j) x u v -
        (endCylinderMetric e t).inner x u v)
  rw [endCylinderMetric_inner, endCylinderParameter, if_pos ht.2]

end PoincareConjecture.M34
