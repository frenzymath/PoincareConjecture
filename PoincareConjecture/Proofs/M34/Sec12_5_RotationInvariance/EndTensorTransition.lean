import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndChartTransition
import PoincareConjecture.Proofs.M34.Standard.LocalIsometryDifferences











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)



theorem endReferenceTransition_mfderiv_isInvertible (p : endReferenceRegion e)
    (r : ℝ) (hr : -3 < r) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∀ x : endReferenceRegion e, x ∈ endReferenceOverlap e r →
      (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) x).IsInvertible := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  intro x hx
  rw [endReferenceTransition_mfderiv e p r hr x hx]
  exact endReferenceTranslation_mfderiv_isInvertible e hr x.property



theorem endReferenceTransition_connection_difference {J J' : Set ℝ}
    (F : RicciFlow 3 StandardCapSpace J) (F' : RicciFlow 3 StandardCapSpace J')
    (p : endReferenceRegion e) (r : ℝ) (hr : -3 < r) (s : ℝ) (hs : -3 < s)
    (hrs : -3 < r + s) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∀ (t : ℝ) (x : endReferenceRegion e), x ∈ endReferenceOverlap e r →
      ∀ u v : TangentSpace (𝓡 3) x,
        CovariantDerivative.difference ((endPullbackFlow e F (r + s) hrs).connection t).connection
          ((endPullbackFlow e F' (r + s) hrs).connection t).connection x u v =
          (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) (x : StandardCapSpace)).inverse
            (CovariantDerivative.difference ((endPullbackFlow e F s hs).connection t).connection
              ((endPullbackFlow e F' s hs).connection t).connection (endReferenceTransition e p r x)
                (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) x u)
                (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) x v)) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  intro t x hx u v
  have hU := endReferenceOverlap_isOpen e r hr
  have hf := (endReferenceTransition_contMDiffOn e p r hr x hx).contMDiffAt (hU.mem_nhds hx)
  have hi : ∀ᶠ y in 𝓝 x,
      (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y).IsInvertible := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact endReferenceTransition_mfderiv_isInvertible e p r hr y hy
  have hm {I : Set ℝ} (G : RicciFlow 3 StandardCapSpace I) :
      ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 3) y,
        ((endPullbackFlow e G (r + s) hrs).metric t).inner y a b =
          ((endPullbackFlow e G s hs).metric t).inner (endReferenceTransition e p r y)
            (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y a)
            (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y b) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact endReferenceTransition_metric e G p r hr s hs hrs t y hy
  have hh := LeviCivitaData.connection_difference_eq_of_local_isometries
    ((endPullbackFlow e F (r + s) hrs).connection t)
    ((endPullbackFlow e F' (r + s) hrs).connection t)
    ((endPullbackFlow e F s hs).connection t) ((endPullbackFlow e F' s hs).connection t)
    hf hi (hm F) (hm F') u v
  erw [endReferenceTransition_mfderiv e p r hr x hx] at hh
  exact hh



theorem endReferenceTransition_curvature {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    (p : endReferenceRegion e) (r : ℝ) (hr : -3 < r) (s : ℝ) (hs : -3 < s)
    (hrs : -3 < r + s) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∀ (t : ℝ) (x : endReferenceRegion e), x ∈ endReferenceOverlap e r →
      ∀ u v w : TangentSpace (𝓡 3) x,
        ((endPullbackFlow e F (r + s) hrs).connection t).curvature x u v w =
          (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) (x : StandardCapSpace)).inverse
            (((endPullbackFlow e F s hs).connection t).curvature (endReferenceTransition e p r x)
              (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) x u)
              (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) x v)
              (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) x w)) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  intro t x hx u v w
  have hh := ((endPullbackFlow e F (r + s) hrs).connection t).curvature_eq_of_local_isometry
    ((endPullbackFlow e F s hs).connection t) (endReferenceOverlap_isOpen e r hr)
    (endReferenceTransition_contMDiffOn e p r hr)
    (endReferenceTransition_metric e F p r hr s hs hrs t) hx
    (endReferenceTransition_mfderiv_isInvertible e p r hr x hx) u v w
  erw [endReferenceTransition_mfderiv e p r hr x hx] at hh
  exact hh

end PoincareConjecture.M34
