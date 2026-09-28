import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndPullbackFlow
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.PartialFlowSpatialJetBounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34




theorem partialFlow_endPullback_bounds (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F : PartialStandardCapFlow g0) (e : StandardCylindricalEnd g0.metric)
    {S B : ℝ} (hS : 0 < S) (hSF : S ≤ F.lifetime) (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B)
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∃ a M : ℝ, 0 < a ∧ 1 ≤ M ∧ ∀ (s : ℝ) (hs : -3 < s),
      ∀ t ∈ Ico 0 S, ∀ (p : endReferenceRegion e) (x : StandardCapSpace),
        x ∈ K → x ∈ endReferenceRegion e →
        (∀ j ≤ m, ‖iteratedFDeriv ℝ j
          (((endPullbackFlow e F.flow s hs).metric t).pullbackCoefficients
            (extChartAt (𝓡 3) p).symm) x‖ ≤ M) ∧
        (∀ v : StandardCapSpace, a * ‖v‖ ^ 2 ≤
          ((endPullbackFlow e F.flow s hs).metric t).pullbackCoefficients
            (extChartAt (𝓡 3) p).symm x v v) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  obtain ⟨a, b, ha, _hb, hell⟩ :=
    partialFlow_compactPullback_ellipticity P F hSF hB.le hfull hK
  obtain ⟨M, hM, hjets⟩ :=
    partialFlow_compactPullback_spatialJet_bounds P E0 F hS hSF hB hfull hK m
  refine ⟨a, M, ha, hM, ?_⟩
  intro s hs t ht p x hx hxU
  constructor
  · intro j hj
    rw [endPullbackFlow_iteratedFDeriv e F.flow s hs t p j x hxU]
    exact hjets j hj (endReferenceRegion_isOpen e)
      (endReferenceTranslation_contMDiffOn e hs)
      (fun _ hy => endReferenceTranslation_mfderiv_isInvertible e hs hy)
      (fun _ hy u v => endReferenceTranslation_metric e hs hy u v) t ht x hx hxU
  · intro v
    rw [endPullbackFlow_chart_coefficients e F.flow s hs t p x hxU]
    exact (hell t ht x hx (endAxialTranslation e s)
      (fun u v => endReferenceTranslation_metric e hs hxU u v) v).1

end PoincareConjecture.M34
