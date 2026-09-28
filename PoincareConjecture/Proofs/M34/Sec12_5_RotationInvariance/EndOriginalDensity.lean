import PoincareConjecture.Proofs.M34.Standard.CanonicalDifferenceDensity
import PoincareConjecture.Proofs.M34.Standard.CanonicalPullbackTensors
import PoincareConjecture.Proofs.M34.Standard.ReverseCoordinateTransport
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndFixedDerivativeBounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy




theorem exists_endOriginal_density_bounds
    {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)
    {dH dA dS : ℕ} (qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    (s : ℝ) (hs : -3 < s) {K : Set StandardCapSpace} (hK : IsCompact K)
    (hKU : K ⊆ endReferenceRegion e) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J J' : Set ℝ}
      (F : RicciFlow 3 StandardCapSpace J) (F' : RicciFlow 3 StandardCapSpace J')
      (p : endReferenceRegion e) (t : ℝ) (x : StandardCapSpace), x ∈ K →
      let dEnd := canonicalDifferenceDensity (endReferenceRegion e) (endReferenceRegion_isOpen e)
        qH qA qS (endPullbackFlow e F s hs) (endPullbackFlow e F' s hs) p t x
      let dOriginal := actualDifferenceEnergyDensity qH qA qS
        (F.connection t) (F'.connection t) (endAxialTranslation e s x)
      dEnd ≤ C * dOriginal ∧ dOriginal ≤ C * dEnd := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  obtain ⟨M, hM, hnorm⟩ := exists_endFixed_derivative_inverse_bound e s hs hK hKU
  obtain ⟨Df, hDf, hforward⟩ := exists_coordinate_transport_density_bound qH qA qS
    (show 0 ≤ M by linarith)
  obtain ⟨Dr, hDr, hreverse⟩ := exists_reverse_coordinate_transport_density_bound qH qA qS
    (show 0 ≤ M by linarith)
  refine ⟨max Df Dr, hDf.trans (le_max_left _ _), ?_⟩
  intro J J' F F' p t x hx dEnd dOriginal
  let xU : endReferenceRegion e := ⟨x, hKU hx⟩
  let f : endReferenceRegion e → StandardCapSpace := fun y => endAxialTranslation e s y
  let hf := endReferenceTranslation_isLocalDiffeomorph e hs
  let F0 := endPullbackFlow e F s hs
  let F1 := endPullbackFlow e F' s hs
  let L : V 3 →L[ℝ] V 3 := mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e s) x
  have hdf : mfderiv (𝓡 3) (𝓡 3) f xU = L :=
    canonicalOpen_mfderiv_restrict (endReferenceRegion_isOpen e) (𝓡 3)
      (((endReferenceTranslation_contMDiffOn e hs x (hKU hx)).contMDiffAt
        ((endReferenceRegion_isOpen e).mem_nhds (hKU hx))).mdifferentiableAt (by simp))
  have hLi : L.IsInvertible := endReferenceTranslation_mfderiv_isInvertible e hs (hKU hx)
  obtain ⟨hL, hLinv⟩ := hnorm x hx
  let H : FH 3 := (F0.metric t).inner xU - (F1.metric t).inner xU
  let H' : FH 3 := (F.metric t).inner (endAxialTranslation e s x) -
    (F'.metric t).inner (endAxialTranslation e s x)
  let A : FA 3 := CovariantDerivative.difference (F0.connection t).connection
    (F1.connection t).connection xU
  let A' : FA 3 := CovariantDerivative.difference (F.connection t).connection
    (F'.connection t).connection (endAxialTranslation e s x)
  let S : FS 3 := curvatureTrilinearMap (F0.connection t) xU -
    curvatureTrilinearMap (F1.connection t) xU
  let S' : FS 3 := curvatureTrilinearMap (F.connection t) (endAxialTranslation e s x) -
    curvatureTrilinearMap (F'.connection t) (endAxialTranslation e s x)
  have hH : ∀ u v, H u v = H' (L u) (L v) := by
    intro u v
    change ((endPullbackFlow e F s hs).metric t).inner xU u v -
      ((endPullbackFlow e F' s hs).metric t).inner xU u v = _
    rw [endPullbackFlow_inner e F s hs t xU, endPullbackFlow_inner e F' s hs t xU]
    rfl
  have hA : ∀ u v, A u v = L.inverse (A' (L u) (L v)) := by
    intro u v
    have hh := canonicalDomain_pullback_connection_difference (endReferenceRegion e)
      (endReferenceRegion_isOpen e) f hf F F' t xU u v
    erw [hdf] at hh
    exact hh
  have hR {I : Set ℝ} (G : RicciFlow 3 StandardCapSpace I) (u v w : V 3) :
      curvatureTrilinearMap ((endPullbackFlow e G s hs).connection t) xU u v w =
        L.inverse (curvatureTrilinearMap (G.connection t) (endAxialTranslation e s x)
          (L u) (L v) (L w)) := by
    have hh := canonicalDomain_pullback_curvature (endReferenceRegion e)
      (endReferenceRegion_isOpen e) f hf G t xU u v w
    erw [hdf] at hh
    exact (curvatureTrilinearMap_apply ((endPullbackFlow e G s hs).connection t) xU u v w).trans
      (hh.trans (congrArg L.inverse
        (curvatureTrilinearMap_apply (G.connection t) (endAxialTranslation e s x)
          (L u) (L v) (L w)).symm))
  have hS : ∀ u v w, S u v w = L.inverse (S' (L u) (L v) (L w)) := by
    intro u v w
    change curvatureTrilinearMap (F0.connection t) xU u v w -
      curvatureTrilinearMap (F1.connection t) xU u v w =
        L.inverse (curvatureTrilinearMap (F.connection t) (endAxialTranslation e s x)
          (L u) (L v) (L w) - curvatureTrilinearMap (F'.connection t)
            (endAxialTranslation e s x) (L u) (L v) (L w))
    rw [hR F, hR F', map_sub]
  have hfwd := hforward L hL hLinv H H' A A' S S' hH hA hS
  have hrev := hreverse L hLi hL hLinv H H' A A' S S' hH hA hS
  have hd : dEnd = actualDifferenceEnergyDensity qH qA qS
      (F0.connection t) (F1.connection t) xU :=
    canonicalDifferenceDensity_coe (endReferenceRegion e) (endReferenceRegion_isOpen e)
      qH qA qS F0 F1 p t xU
  rw [hd]
  constructor
  · exact hfwd.trans (mul_le_mul_of_nonneg_right (le_max_left Df Dr)
      (actualDifferenceEnergyDensity_nonneg qH qA qS (F.connection t) (F'.connection t)
        (endAxialTranslation e s x)))
  · exact hrev.trans (mul_le_mul_of_nonneg_right (le_max_right Df Dr)
      (actualDifferenceEnergyDensity_nonneg qH qA qS (F0.connection t) (F1.connection t) xU))

end PoincareConjecture.M34
