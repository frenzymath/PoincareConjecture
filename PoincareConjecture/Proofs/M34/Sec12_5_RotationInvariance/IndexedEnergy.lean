import PoincareConjecture.Proofs.M34.Standard.CanonicalDifferenceEnergy
import PoincareConjecture.Proofs.M34.Standard.CanonicalCoreFlow
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndPullbackFlow
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EnergyCutoffs










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

open DifferenceEnergy

variable {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)
  {dH dA dS : ℕ} (qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
  (qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
  (qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
  {J J' : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
  (F' : RicciFlow 3 StandardCapSpace J') (p : endReferenceRegion e)



noncomputable def capDifferenceEnergy : ℕ → ℝ → ℝ :=
  letI := (isOpen_univ : IsOpen (univ : Set (V 3))).isOpenEmbedding_subtypeVal.singletonChartedSpace
  letI := (isOpen_univ : IsOpen (univ : Set (V 3))).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  fun i => match i with
  | 0 => canonicalDifferenceEnergy univ isOpen_univ qH qA qS (coreEnergyCutoff e)
      (canonicalCoreFlow F) (canonicalCoreFlow F') ⟨0, mem_univ _⟩
  | j + 1 => canonicalDifferenceEnergy (endReferenceRegion e) (endReferenceRegion_isOpen e)
      qH qA qS (endEnergyCutoff e)
      (endPullbackFlow e F j (by have := Nat.cast_nonneg (α := ℝ) j; linarith))
      (endPullbackFlow e F' j (by have := Nat.cast_nonneg (α := ℝ) j; linarith)) p



theorem capDifferenceEnergy_nonneg (i : ℕ) (t : ℝ) :
    0 ≤ capDifferenceEnergy e qH qA qS F F' p i t := by
  cases i <;> exact canonicalDifferenceEnergy_nonneg _ _ qH qA qS _ _ _ _ t



theorem capDifferenceEnergy_continuousOn {K : Set ℝ} (hK : IsCompact K)
    (hKJ : K ⊆ J ∩ J') (i : ℕ) :
    ContinuousOn (capDifferenceEnergy e qH qA qS F F' p i) K := by
  cases i with
  | zero =>
    exact canonicalDifferenceEnergy_continuousOn univ isOpen_univ qH qA qS
      (energyCutoffs_contDiff e).2.continuous (energyCutoffs_hasCompactSupport e).2
      (subset_univ _) _ _ _ hK hKJ
  | succ j =>
    exact canonicalDifferenceEnergy_continuousOn
      (endReferenceRegion e) (endReferenceRegion_isOpen e) qH qA qS
      (energyCutoffs_contDiff e).1.continuous (energyCutoffs_hasCompactSupport e).1
      (endEnergyCutoff_tsupport_subset_region e) _ _ _ hK hKJ



theorem capDifferenceEnergy_differentiableAt {t : ℝ} (ht : t ∈ interior (J ∩ J'))
    (i : ℕ) : DifferentiableAt ℝ (capDifferenceEnergy e qH qA qS F F' p i) t := by
  cases i with
  | zero =>
    exact canonicalDifferenceEnergy_differentiableAt univ isOpen_univ qH qA qS
      (energyCutoffs_contDiff e).2.continuous (energyCutoffs_hasCompactSupport e).2
      (subset_univ _) _ _ _ ht
  | succ j =>
    exact canonicalDifferenceEnergy_differentiableAt
      (endReferenceRegion e) (endReferenceRegion_isOpen e) qH qA qS
      (energyCutoffs_contDiff e).1.continuous (energyCutoffs_hasCompactSupport e).1
      (endEnergyCutoff_tsupport_subset_region e) _ _ _ ht

end PoincareConjecture.M34
