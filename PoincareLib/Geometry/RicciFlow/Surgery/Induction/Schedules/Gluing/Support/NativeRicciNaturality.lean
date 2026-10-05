import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Homothety
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Normalization
import PoincareLib.Geometry.RicciFlow.Limit.RicciConvergence
import PoincareLib.Geometry.Riemannian.Metric.LocalExtension
import PoincareLib.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.Equation
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scalar.Calculus.RicciJetNorm
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scalar.Bounds.ScalarScaling

/-!
# Native Ricci under local constant metric homotheties

Morgan--Tian Definition 2.16, p. 30, equation (3.7), p. 41, and Proposition
15.2, pp. 353-354. Realize the actual positive metric germs and transport
their Ricci tensors. Constant scaling cancels in the covariant Ricci tensor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Native two-jets and the bilinear pullback contain nested linear slots.
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M45

open SpacetimeBounds M44

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

/-- The native Ricci tensor is natural under the actual local map and
unchanged by a positive constant metric factor. Proposition 15.2,
pp. 353-354, and Definition 3.40, p. 61. -/
theorem nativeRicci_local_homothety {n : ℕ}
    {A C : E n → MetricCoefficient n} {phi : E n → E n}
    {U V : Set (E n)} (hU : IsOpen U) (hV : IsOpen V)
    {x : E n} (hx : x ∈ U) (hphiV : phi x ∈ V)
    (hA : ContDiffOn ℝ ∞ A U) (hC : ContDiffOn ℝ ∞ C V)
    (hAs : ∀ y ∈ U, ∀ v w, A y v w = A y w v)
    (hAp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < A y v v)
    (hCs : ∀ y ∈ V, ∀ v w, C y v w = C y w v)
    (hCp : ∀ y ∈ V, ∀ v, v ≠ 0 → 0 < C y v v)
    (hphi : ContDiffAt ℝ ∞ phi x)
    (hinv : ∀ᶠ y in 𝓝 x, (fderiv ℝ phi y).IsInvertible)
    {r : ℝ} (hr : 0 < r)
    (hmetric : A =ᶠ[𝓝 x] (fun y => r • (C (phi y)).bilinearComp
      (fderiv ℝ phi y) (fderiv ℝ phi y))) :
    jetRicciBilinear (metricTwoJet A x) =
      (jetRicciBilinear (metricTwoJet C (phi x))).bilinearComp
        (fderiv ℝ phi x) (fderiv ℝ phi x) := by
  obtain ⟨gA, DA, UA, hUA, hxA, _, heqA⟩ :=
    RiemannianMetric.exists_local_realization hU hx A hA hAs hAp
  obtain ⟨gC, DC, UC, hUC, hxC, _, heqC⟩ :=
    RiemannianMetric.exists_local_realization hV hphiV C hC hCs hCp
  have hgA : gA.euclideanCoefficients =ᶠ[𝓝 x] A :=
    eventually_of_mem (hUA.mem_nhds hxA) heqA
  have hgC : gC.euclideanCoefficients =ᶠ[𝓝 (phi x)] C :=
    eventually_of_mem (hUC.mem_nhds hxC) heqC
  let gR := m01RescaledMetric gC r hr
  let DR := m01RescaledMetric_connection gC DC r hr
  have hm : ∀ᶠ y in 𝓝 x, ∀ v w : E n, gA.inner y v w =
      gR.inner (phi y) (mfderiv (𝓡 n) (𝓡 n) phi y v)
        (mfderiv (𝓡 n) (𝓡 n) phi y w) := by
    filter_upwards [hgA, hgC.comp_tendsto hphi.continuousAt, hmetric] with y hAy hCy hmy v w
    change gC.euclideanCoefficients (phi y) = C (phi y) at hCy
    change gA.euclideanCoefficients y v w =
      r * gC.euclideanCoefficients (phi y)
        (mfderiv (𝓡 n) (𝓡 n) phi y v) (mfderiv (𝓡 n) (𝓡 n) phi y w)
    rw [hAy, hmy, hCy]
    simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.bilinearComp_apply,
      mfderiv_eq_fderiv]
    rfl
  have hi : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) phi y).IsInvertible := by
    simpa only [mfderiv_eq_fderiv] using hinv
  have hscaled (v w : E n) : DR.ricci (phi x) v w = DC.ricci (phi x) v w := by
    have h := M13.homothety_ricci_eq gC gR (Diffeomorph.refl (𝓡 n) (E n) ∞)
      r hr (rescaledMetric_identity_homothety hr) DC DR (phi x) v w
    simpa only [Diffeomorph.coe_refl, mfderiv_id, ContinuousLinearMap.id_apply, id_eq] using h
  rw [← metricTwoJet_congr_of_eventuallyEq hgA,
    ← metricTwoJet_congr_of_eventuallyEq hgC,
    jetRicciBilinear_metricTwoJet DA, jetRicciBilinear_metricTwoJet DC]
  ext v w
  change DA.ricci x v w = DC.ricci (phi x) (fderiv ℝ phi x v) (fderiv ℝ phi x w)
  have h := DA.ricci_eq_pullback_euclidean DR hphi.contMDiffAt hi hm v w
  rw [hscaled] at h
  convert h using 1
  rw [mfderiv_eq_fderiv]
  rfl

end PoincareMT.M45
