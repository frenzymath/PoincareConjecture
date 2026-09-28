import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.IndexedEnergy
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.TranslatedEnergyCutoffs
import PoincareConjecture.Proofs.M34.Standard.EqualMetricDifferenceEnergy
import PoincareConjecture.Proofs.M34.Standard.CanonicalEnergyMetricDetection
import PoincareConjecture.Proofs.M34.Mathlib.RiemannianMetricExt

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

theorem capDifferenceEnergy_eq_zero_of_metric_eq {t : ℝ} (h : F.metric t = F'.metric t)
    (i : ℕ) : capDifferenceEnergy e qH qA qS F F' p i t = 0 := by
  let := (isOpen_univ : IsOpen (univ : Set (V 3))).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (isOpen_univ : IsOpen (univ : Set (V 3))).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  cases i with
  | zero =>
    apply canonicalDifferenceEnergy_eq_zero_of_metric_eq _ _ qH qA qS _ _ _ _ t
    apply Bundle.ContMDiffRiemannianMetric.eq_of_inner_eq
    intro x
    rw [canonicalCoreFlow_inner, canonicalCoreFlow_inner, h]
  | succ j =>
    apply canonicalDifferenceEnergy_eq_zero_of_metric_eq _ _ qH qA qS _ _ _ _ t
    apply Bundle.ContMDiffRiemannianMetric.eq_of_inner_eq
    intro x
    rw [endPullbackFlow_inner, endPullbackFlow_inner, h]

theorem metric_eq_of_capDifferenceEnergy_zero {t : ℝ} (ht : t ∈ J ∩ J')
    (hz : ∀ i, capDifferenceEnergy e qH qA qS F F' p i t = 0) :
    F.metric t = F'.metric t := by
  let := (isOpen_univ : IsOpen (univ : Set (V 3))).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (isOpen_univ : IsOpen (univ : Set (V 3))).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  apply Bundle.ContMDiffRiemannianMetric.eq_of_inner_eq
  intro x
  rcases energyCutoffs_plateau_cover e x with hc | ⟨j, hj⟩
  · have hh := canonicalDifferenceEnergy_metric_eq_of_zero univ isOpen_univ qH qA qS
      (energyCutoffs_contDiff e).2.continuous (energyCutoffs_hasCompactSupport e).2
      (subset_univ _) (canonicalCoreFlow F) (canonicalCoreFlow F') ⟨0, mem_univ _⟩
      ht (hz 0) ⟨x, mem_univ _⟩ (by simpa only [hc] using one_ne_zero)
    simpa only [canonicalCoreFlow_inner] using hh
  · have hx : x ∈ tsupport (translatedEnergyCutoff e j) :=
      subset_tsupport _ (by simpa only [Function.mem_support, hj] using one_ne_zero)
    obtain ⟨y, hy, hyx, hcut⟩ := translatedEnergyCutoff_localization e j hx
    subst x
    have hs : -3 < (j : ℝ) := by have := Nat.cast_nonneg (α := ℝ) j; linarith
    have hh := canonicalDifferenceEnergy_metric_eq_of_zero
      (endReferenceRegion e) (endReferenceRegion_isOpen e) qH qA qS
      (energyCutoffs_contDiff e).1.continuous (energyCutoffs_hasCompactSupport e).1
      (endEnergyCutoff_tsupport_subset_region e)
      (endPullbackFlow e F j hs) (endPullbackFlow e F' j hs) p ht (hz (j + 1))
      ⟨y, hy⟩ (by simpa only [hcut, hj] using one_ne_zero)
    rw [endPullbackFlow_inner, endPullbackFlow_inner] at hh
    obtain ⟨L, hL⟩ := endReferenceTranslation_mfderiv_isInvertible e hs hy
    ext u v
    have heq := congrArg (fun B : FH 3 => B (L.symm u) (L.symm v)) hh
    change (F.metric t).inner (endAxialTranslation e j y)
      (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e j) y (L.symm u))
      (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e j) y (L.symm v)) =
      (F'.metric t).inner (endAxialTranslation e j y)
      (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e j) y (L.symm u))
      (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e j) y (L.symm v)) at heq
    rw [← hL] at heq
    simpa only [ContinuousLinearEquiv.coe_coe, L.apply_symm_apply] using heq

end PoincareConjecture.M34
