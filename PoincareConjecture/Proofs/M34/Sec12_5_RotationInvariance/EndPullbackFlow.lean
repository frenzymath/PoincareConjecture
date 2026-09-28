import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndLocalDiffeomorph
import PoincareConjecture.Proofs.M34.Standard.CanonicalPullbackCoefficients










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)



theorem endReferenceTranslation_contMDiffOn {s : ℝ} (hs : -3 < s) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (endAxialTranslation e s) (endReferenceRegion e) := by
  rintro _ ⟨z, hz, rfl⟩
  have hh : 3 < z.2 := hz.2.1
  exact (endAxialTranslation_contMDiffAt e s (by linarith)
    (by linarith)).contMDiffWithinAt



theorem endReferenceTranslation_metric {s : ℝ} (hs : -3 < s)
    {x : StandardCapSpace} (hx : x ∈ endReferenceRegion e)
    (u v : TangentSpace (𝓡 3) x) :
    g.inner x u v = g.inner (endAxialTranslation e s x)
      (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e s) x u)
      (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e s) x v) := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hh : 3 < z.2 := hz.2.1
  exact endAxialTranslation_metric e s (by linarith) (by linarith) u v



theorem endReferenceTranslation_mfderiv_isInvertible {s : ℝ} (hs : -3 < s)
    {x : StandardCapSpace} (hx : x ∈ endReferenceRegion e) :
    (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e s) x).IsInvertible := by
  have hbij := g.mfderiv_bijective_of_pullback_eq g x
    (fun u v => (endReferenceTranslation_metric e hs hx u v).symm)
  let L : StandardCapSpace →L[ℝ] StandardCapSpace :=
    mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e s) x
  exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hbij.1)
    (LinearMap.range_eq_top.mpr hbij.2), rfl⟩



noncomputable def endPullbackFlow {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    (s : ℝ) (hs : -3 < s) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    RicciFlow 3 (endReferenceRegion e) J :=
  F.pullbackToCanonicalDomain (endReferenceRegion e) (endReferenceRegion_isOpen e)
    (fun x => endAxialTranslation e s x) (endReferenceTranslation_isLocalDiffeomorph e hs)



theorem endPullbackFlow_inner {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    (s : ℝ) (hs : -3 < s) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∀ (t : ℝ) (x : endReferenceRegion e),
      ((endPullbackFlow e F s hs).metric t).inner x =
        (F.metric t).pullbackCoefficients (endAxialTranslation e s) x :=
  canonicalDomain_flow_inner (endReferenceRegion e) (endReferenceRegion_isOpen e)
    (endAxialTranslation e s) (endReferenceTranslation_contMDiffOn e hs)
    (endReferenceTranslation_isLocalDiffeomorph e hs) F



theorem endPullbackFlow_chart_coefficients {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    (s : ℝ) (hs : -3 < s) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∀ (t : ℝ) (p : endReferenceRegion e) (x : StandardCapSpace), x ∈ endReferenceRegion e →
      ((endPullbackFlow e F s hs).metric t).pullbackCoefficients
        (extChartAt (𝓡 3) p).symm x =
          (F.metric t).pullbackCoefficients (endAxialTranslation e s) x := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  intro t p x hx
  exact canonicalDomain_pullback_chart_coefficients (endReferenceRegion e)
    (endReferenceRegion_isOpen e) (endAxialTranslation e s)
    (endReferenceTranslation_contMDiffOn e hs)
    (endReferenceTranslation_isLocalDiffeomorph e hs) (F.metric t) p ⟨x, hx⟩



theorem endPullbackFlow_iteratedFDeriv {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    (s : ℝ) (hs : -3 < s) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∀ (t : ℝ) (p : endReferenceRegion e) (j : ℕ) (x : StandardCapSpace),
      x ∈ endReferenceRegion e →
      iteratedFDeriv ℝ j (((endPullbackFlow e F s hs).metric t).pullbackCoefficients
        (extChartAt (𝓡 3) p).symm) x =
          iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients (endAxialTranslation e s)) x := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  intro t p j x hx
  have heq : ((endPullbackFlow e F s hs).metric t).pullbackCoefficients
      (extChartAt (𝓡 3) p).symm =ᶠ[𝓝 x]
        (F.metric t).pullbackCoefficients (endAxialTranslation e s) := by
    filter_upwards [(endReferenceRegion_isOpen e).mem_nhds hx] with y hy
    exact endPullbackFlow_chart_coefficients e F s hs t p y hy
  exact (heq.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds

end PoincareConjecture.M34
