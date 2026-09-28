import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.TruncatedGramCurvature
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.AnnulusBoundaryFluxLimit

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

local notation "S" => Set.ofPred (fun p : LoopPlane => p 1 ∈ Icc (0 : ℝ) 1)

theorem annulus_boundary_curvature_le (D : LeviCivitaData g) (A : M64Annulus g c0 c1)
    {r : ℝ} (hr : 0 < r) (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hAc : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S)
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusOpenStrip)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hinj : ∀ p ∈ m64AnnulusDomain,
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain p))
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ p ∈ m64AnnulusInterior, D.sectionalCurvature (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K)
    (c : Bool → ℝ → M) (sigma : Bool → ℝ → ℝ)
    (hc : ∀ u, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (c u))
    (hcv : ∀ u s, curveVelocity (n := n) (c u) s ≠ 0)
    (hsigma : ∀ u, ContDiff ℝ 1 (sigma u)) (hmono : ∀ u, Monotone (sigma u))
    (htrace : ∀ u s, A.map (annulusPoint s (if u then 1 else 0)) = c u (sigma u s)) :
    let kappa := fun u s => (g.tangentNorm (c u s) (curveVelocity (n := n) (c u) s))⁻¹ •
      rampHorizontalCovariantDerivative D (c u)
        (fun y => (g.tangentNorm (c u y) (curveVelocity (n := n) (c u) y))⁻¹ •
          curveVelocity (n := n) (c u) y) s
    let C := fun (u : Bool) theta =>
      let p := annulusPoint theta (if u then 1 else 0)
      g.inner (A.map p) (kappa u (sigma u theta))
        (mfderivWithin (𝓡 2) (𝓡 n) A.map S p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
    (∀ u, IntervalIntegrable (C u) volume 0 curvePeriod) ∧
      r⁻¹ * ((∫ theta in (0 : ℝ)..curvePeriod, C true theta) -
        ∫ theta in (0 : ℝ)..curvePeriod, C false theta) ≤ K * A.area := by
  let kappa := fun u s => (g.tangentNorm (c u s) (curveVelocity (n := n) (c u) s))⁻¹ •
    rampHorizontalCovariantDerivative D (c u)
      (fun y => (g.tangentNorm (c u y) (curveVelocity (n := n) (c u) y))⁻¹ •
        curveVelocity (n := n) (c u) y) s
  let C := fun (u : Bool) theta =>
    let p := annulusPoint theta (if u then 1 else 0)
    g.inner (A.map p) (kappa u (sigma u theta))
      (mfderivWithin (𝓡 2) (𝓡 n) A.map S p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
  let L := fun (u : Bool) (h theta : ℝ) =>
    (if u then 1 else -1) *
      fderiv ℝ (fun p => Real.log (m60AreaGram g A.map p 0 0))
        (annulusPoint theta (if u then 1 - h else h)) (EuclideanSpace.basisFun (Fin 2) ℝ 1) / 2
  obtain ⟨hB, h, hh, -, -, hconv⟩ := annulus_boundary_flux_limits D A hr hminimum
    hAc hAi hconformal hinj c sigma hc hcv hsigma hmono htrace
  have hC (u : Bool) : IntervalIntegrable (C u) volume 0 curvePeriod := by
    have hu := hB u
    change IntervalIntegrable (fun theta => (if u then -1 else 1) * C u theta)
      volume 0 curvePeriod at hu
    cases u
    · simpa only [Bool.false_eq_true, if_false, one_mul] using hu
    · apply hu.neg.congr
      intro theta _
      change -((-1 : ℝ) * C true theta) = C true theta
      ring
  have hcl (u : Bool) :
      Tendsto (fun k => ∫ theta in (0 : ℝ)..curvePeriod, L u (h k) theta) atTop
        (𝓝 ((if u then -1 else 1) * ∫ theta in (0 : ℝ)..curvePeriod, C u theta)) := by
    have hu := hconv u
    change Tendsto (fun k => ∫ theta in (0 : ℝ)..curvePeriod, L u (h k) theta) atTop
      (𝓝 (∫ theta in (0 : ℝ)..curvePeriod, (if u then -1 else 1) * C u theta)) at hu
    simpa only [intervalIntegral.integral_const_mul] using hu
  have hlimit := ((hcl false).add (hcl true)).const_mul (-r⁻¹)
  simp only [Bool.false_eq_true, if_false, if_true, one_mul, neg_one_mul] at hlimit
  have hbound : -r⁻¹ *
      ((∫ theta in (0 : ℝ)..curvePeriod, C false theta) +
        -(∫ theta in (0 : ℝ)..curvePeriod, C true theta)) ≤ K * A.area := by
    apply le_of_tendsto hlimit
    apply Eventually.of_forall
    intro k
    have hraw := annulus_truncated_gram_curvature_le D A hr hminimum hconformal hAc hAi
      hinj (lo := h k) (hi := 1 - h k) (hh k).1
        (by linarith [(hh k).2]) (by linarith [(hh k).1]) hK hsec
    simp only [L, Bool.false_eq_true, if_false, if_true, one_mul, neg_one_mul,
      intervalIntegral.integral_div, intervalIntegral.integral_neg,
      EuclideanSpace.basisFun_apply]
    nlinarith only [hraw]
  exact ⟨hC, by nlinarith only [hbound]⟩

end PoincareConjecture.M64
