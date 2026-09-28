import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.AnnulusBoundaryCollar
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.FiniteScaledCollar

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64

open M65Branch M65StrictTrace M65Gauss

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

local notation "S" => Set.ofPred (fun p : LoopPlane => p 1 ∈ Icc (0 : ℝ) 1)

set_option maxHeartbeats 1400000 in

theorem annulus_boundary_flux_limits (D : LeviCivitaData g) (A : M64Annulus g c0 c1)
    {r : ℝ} (hr : 0 < r) (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hAc : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S)
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusOpenStrip)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hinj : ∀ p ∈ m64AnnulusDomain,
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain p))
    (c : Bool → ℝ → M) (sigma : Bool → ℝ → ℝ)
    (hc : ∀ u, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (c u))
    (hcv : ∀ u s, curveVelocity (n := n) (c u) s ≠ 0)
    (hsigma : ∀ u, ContDiff ℝ 1 (sigma u)) (hmono : ∀ u, Monotone (sigma u))
    (htrace : ∀ u s, A.map (annulusPoint s (if u then 1 else 0)) = c u (sigma u s)) :
    let kappa := fun u s => (g.tangentNorm (c u s) (curveVelocity (n := n) (c u) s))⁻¹ •
      rampHorizontalCovariantDerivative D (c u)
        (fun y => (g.tangentNorm (c u y) (curveVelocity (n := n) (c u) y))⁻¹ •
          curveVelocity (n := n) (c u) y) s
    let B := fun (u : Bool) theta =>
      let p := annulusPoint theta (if u then 1 else 0)
      (if u then -1 else 1) * g.inner (A.map p) (kappa u (sigma u theta))
        (mfderivWithin (𝓡 2) (𝓡 n) A.map S p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
    let L := fun (u : Bool) (h theta : ℝ) =>
      (if u then 1 else -1) *
        fderiv ℝ (fun p => Real.log (m60AreaGram g A.map p 0 0))
          (annulusPoint theta (if u then 1 - h else h)) (EuclideanSpace.basisFun (Fin 2) ℝ 1) / 2
    (∀ u, IntervalIntegrable (B u) volume 0 curvePeriod) ∧
      ∃ h : ℕ → ℝ, (∀ k, h k ∈ Ioo (0 : ℝ) (1 / 2)) ∧ Tendsto h atTop (𝓝 0) ∧
        (∀ u k, IntervalIntegrable (L u (h k)) volume 0 curvePeriod) ∧
        ∀ u, Tendsto (fun k => ∫ theta in (0 : ℝ)..curvePeriod, L u (h k) theta) atTop
          (𝓝 (∫ theta in (0 : ℝ)..curvePeriod, B u theta)) := by
  classical
  let P := fun u x => annulusBoundarySource r hr.ne' u x
  let H := fun u x => (chartAt (EuclideanSpace ℝ (Fin n))
    (A.map (annulusPoint x (if u then 1 else 0)))) ∘ A.map ∘ P u x
  let kappa := fun u s => (g.tangentNorm (c u s) (curveVelocity (n := n) (c u) s))⁻¹ •
    rampHorizontalCovariantDerivative D (c u)
      (fun y => (g.tangentNorm (c u y) (curveVelocity (n := n) (c u) y))⁻¹ •
        curveVelocity (n := n) (c u) y) s
  let B := fun (u : Bool) theta =>
    let p := annulusPoint theta (if u then 1 else 0)
    (if u then -1 else 1) * g.inner (A.map p) (kappa u (sigma u theta))
      (mfderivWithin (𝓡 2) (𝓡 n) A.map S p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
  let L := fun (u : Bool) (h theta : ℝ) =>
    (if u then 1 else -1) *
      fderiv ℝ (fun p => Real.log (m60AreaGram g A.map p 0 0))
        (annulusPoint theta (if u then 1 - h else h)) (EuclideanSpace.basisFun (Fin 2) ℝ 1) / 2
  choose gE DE d e C V _hd hd1 he heD hC hH hV hVi hDV hholder hinside hboundary using
    fun (u : Bool) (x : ℝ) => annulus_regular_boundary_collar D A hr x u
      hminimum hAc hAi hconformal hinj (hc u) (hcv u) (hsigma u) (hmono u) (htrace u)
  have hinside' (u : Bool) (x : ℝ)
      (z : ℂ) (hz : z ∈ ball (0 : ℂ) (d u x) ∩ {z | 0 < z.im}) :
      (gE u x).inner (H u x z)
        (covariantDerivativeAlongMap (DE u x) (H u x) (fun w => (V u x w).1) z 1)
        (V u x z).2 = L u z.im (x + r * z.re) := by
    simpa only [H, P, L, annulusBoundarySource_apply] using hinside u x z hz
  have hperiod : 0 < curvePeriod := by unfold curvePeriod; positivity
  exact finite_scaled_boundary_collar_limit hperiod hr gE DE H V d e C B L he heD hd1 hC
    hH hV hVi hDV hholder hinside' hboundary

end PoincareConjecture.M64
