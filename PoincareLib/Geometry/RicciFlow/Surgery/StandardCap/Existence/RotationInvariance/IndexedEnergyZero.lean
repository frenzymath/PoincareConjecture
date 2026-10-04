import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.RotationInvariance.IndexedEnergy
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.RotationInvariance.TranslatedEnergyCutoffs
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Energy.EqualMetricDifferenceEnergy
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Energy.CanonicalEnergyMetricDetection
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Metric.RiemannianMetricExt

/-!
# Metric equality and vanishing of the indexed actual energies

Whole-metric equality annihilates the actual tensor differences. In the
reverse direction the plateau cover and the genuine invertible end
derivative return equality at each original point. This is Morgan-Tian
Section 12.5, pp. 309-319 and uniqueness-assembly-interfaces.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Actual curvature takes values in three nested Hom spaces.
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34

open DifferenceEnergy

variable {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)
  {dH dA dS : ℕ} (qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
  (qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
  (qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
  {J J' : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
  (F' : RicciFlow 3 StandardCapSpace J') (p : endReferenceRegion e)

/-- Equal whole slices have zero core and end energies, with no equality
assumed between compatible connection records (Section 12.5, pp. 309-319). -/
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

/-- Vanishing of the actual indexed energies at an included common time
forces equality of the original metrics everywhere
(Section 12.5, pp. 309-319). -/
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

end PoincareMT.M34
