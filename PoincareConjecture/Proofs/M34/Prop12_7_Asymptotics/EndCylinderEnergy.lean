import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderCompatibility
import PoincareConjecture.Proofs.M34.Standard.EqualMetricDifferenceEnergy
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.CompatibleEndNeighbors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

open DifferenceEnergy

variable {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)
  {dH dA dS : ℕ} (qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
  (qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
  (qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
  {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) (p : endReferenceRegion e)

noncomputable def endCylinderDifferenceEnergy (j : ℕ) : ℝ → ℝ :=
  letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  canonicalDifferenceEnergy (endReferenceRegion e) (endReferenceRegion_isOpen e)
    qH qA qS (endEnergyCutoff e)
    (endPullbackFlow e F j (by have := Nat.cast_nonneg (α := ℝ) j; linarith))
    (endCylinderFlow e) p

noncomputable def endCylinderDifferenceSupportIntegral (j : ℕ) (t : ℝ) : ℝ :=
  letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  letI : MeasurableSpace StandardCapSpace := borel _
  letI : BorelSpace StandardCapSpace := ⟨rfl⟩
  ∫ x in tsupport (endEnergyCutoff e), canonicalDifferenceDensity
    (endReferenceRegion e) (endReferenceRegion_isOpen e) qH qA qS
    (endPullbackFlow e F j (by have := Nat.cast_nonneg (α := ℝ) j; linarith))
    (endCylinderFlow e) p t x

theorem endCylinderDifferenceEnergy_nonneg (j : ℕ) (t : ℝ) :
    0 ≤ endCylinderDifferenceEnergy e qH qA qS F p j t :=
  canonicalDifferenceEnergy_nonneg _ _ qH qA qS _ _ _ _ t

theorem endCylinderDifferenceEnergy_continuousOn {K : Set ℝ} (hK : IsCompact K)
    (hKJ : K ⊆ J ∩ Ico 0 1) (j : ℕ) :
    ContinuousOn (endCylinderDifferenceEnergy e qH qA qS F p j) K :=
  canonicalDifferenceEnergy_continuousOn
    (endReferenceRegion e) (endReferenceRegion_isOpen e) qH qA qS
    (energyCutoffs_contDiff e).1.continuous (energyCutoffs_hasCompactSupport e).1
    (endEnergyCutoff_tsupport_subset_region e) _ _ _ hK hKJ

theorem endCylinderDifferenceEnergy_differentiableAt {t : ℝ}
    (ht : t ∈ interior (J ∩ Ico 0 1)) (j : ℕ) :
    DifferentiableAt ℝ (endCylinderDifferenceEnergy e qH qA qS F p j) t :=
  canonicalDifferenceEnergy_differentiableAt
    (endReferenceRegion e) (endReferenceRegion_isOpen e) qH qA qS
    (energyCutoffs_contDiff e).1.continuous (energyCutoffs_hasCompactSupport e).1
    (endEnergyCutoff_tsupport_subset_region e) _ _ _ ht

theorem endCylinderDifferenceEnergy_zero (hinit : F.metric 0 = g) (j : ℕ) :
    endCylinderDifferenceEnergy e qH qA qS F p j 0 = 0 :=
  canonicalDifferenceEnergy_eq_zero_of_metric_eq
    (endReferenceRegion e) (endReferenceRegion_isOpen e) qH qA qS (endEnergyCutoff e)
    _ _ p 0 (endPullbackFlow_initial_eq_cylinder e F hinit j
      (by have := Nat.cast_nonneg (α := ℝ) j; linarith))

omit F p in

theorem exists_endCylinderDifferenceSupportIntegral_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
      (p : endReferenceRegion e) {t : ℝ}, t ∈ J ∩ Ico 0 1 → ∀ j : ℕ,
      endCylinderDifferenceSupportIntegral e qH qA qS F p (j + 1) t ≤
        C * (endCylinderDifferenceEnergy e qH qA qS F p j t +
          endCylinderDifferenceEnergy e qH qA qS F p (j + 1) t +
          endCylinderDifferenceEnergy e qH qA qS F p (j + 2) t) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  let : MeasurableSpace StandardCapSpace := borel _
  let : BorelSpace StandardCapSpace := ⟨rfl⟩
  obtain ⟨C, hC, hcompare⟩ := exists_compatibleEnd_neighbor_bound e qH qA qS
  refine ⟨C, hC, ?_⟩
  intro J F p t ht
  have hj (j : ℕ) : -3 < (j : ℝ) := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  apply hcompare (fun j => endPullbackFlow e F j (hj j)) (fun _ => endCylinderFlow e) p ht
  · intro i j r hr hij x hx u v
    have hrpos : -3 < r := by rcases hr with rfl | rfl | rfl <;> norm_num
    have hrs : -3 < r + (j : ℝ) := by rw [← hij]; exact hj i
    simpa only [← hij] using endReferenceTransition_metric e F p r hrpos j (hj j) hrs t x hx u v
  · intro _i _j r hr _hij x hx u v
    have hrpos : -3 < r := by rcases hr with rfl | rfl | rfl <;> norm_num
    exact endCylinderMetric_transition e p r hrpos t x hx u v

end PoincareConjecture.M34
