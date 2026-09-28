import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteForwardCompetitors
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.DoubleProductRicci
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.CircleCurvatureNorm
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.UnitRicciControl

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "S" => Set.ofPred (fun p : LoopPlane => p 1 ∈ Icc (0 : ℝ) 1)

theorem auxiliaryCircle_finite_exists_forward
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (hn : 1 ≤ n)
    (c : Bool → ℝ → ℝ → Q.charts.Point)
    (hc : ∀ u, M63C2ShrinkingCurveOn Q.flow (c u) (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (sigma : Bool → M64PeriodicDegreeOneLift)
    (hsigma : ∀ u, ContDiff ℝ 1 (sigma u).map)
    (A : M64Annulus (Q.flow.metric t)
      ((fun x => c false x t) ∘ (sigma false).map)
      ((fun x => c true x t) ∘ (sigma true).map))
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (Q.flow.metric t)
      (fun x => c false x t) (fun x => c true x t))
    (hAc : ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 A.map S)
    (hAi : ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) ∞ A.map m64AnnulusOpenStrip)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (Q.flow.metric t) A.map p 0 0 =
        r⁻¹ * m60AreaGram (Q.flow.metric t) A.map p 1 1 ∧
      m60AreaGram (Q.flow.metric t) A.map p 0 1 = 0)
    (hinj : ∀ p ∈ m64AnnulusDomain,
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 ((n + 1) + 1)) A.map m64AnnulusDomain p))
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∃ B : M64Annulus (Q.flow.metric (t + h))
          (fun x => c false x (t + h)) (fun x => c true x (t + h)),
        B.area ≤ A.area + h * ((2 * (n : ℝ) - 1) * K * A.area + eta) := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  have hforward := c2_annulus_finite_exists_forward Q.flow c hc ht sigma hsigma A hr
    hminimum hAc hAi hconformal hinj hK
    (fun p _ => (le_abs_self _).trans
      ((auxiliaryCircle_sectional_abs_le P Q t (A.map p) _ _).trans (hcurv (A.map p).1.1)))
    (R := ((n : ℝ) - 1) * K)
    (fun q v => (neg_le_abs _).trans
      (auxiliaryCircle_ricci_quadratic_abs_le P Q hn t hK q (hcurv q.1.1) v))
  have hcoef : K + 2 * (((n : ℝ) - 1) * K) = (2 * (n : ℝ) - 1) * K := by ring
  simpa only [hcoef] using hforward

theorem auxiliaryCircle_finite_exists_forward_of_ambient_bounds
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (hn : 1 ≤ n)
    (c : Bool → ℝ → ℝ → Q.charts.Point)
    (hc : ∀ u, M63C2ShrinkingCurveOn Q.flow (c u) (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (sigma : Bool → M64PeriodicDegreeOneLift)
    (hsigma : ∀ u, ContDiff ℝ 1 (sigma u).map)
    (A : M64Annulus (Q.flow.metric t)
      ((fun x => c false x t) ∘ (sigma false).map)
      ((fun x => c true x t) ∘ (sigma true).map))
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (Q.flow.metric t)
      (fun x => c false x t) (fun x => c true x t))
    (hAc : ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 A.map S)
    (hAi : ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) ∞ A.map m64AnnulusOpenStrip)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (Q.flow.metric t) A.map p 0 0 =
        r⁻¹ * m60AreaGram (Q.flow.metric t) A.map p 1 1 ∧
      m60AreaGram (Q.flow.metric t) A.map p 0 1 = 0)
    (hinj : ∀ p ∈ m64AnnulusDomain,
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 ((n + 1) + 1)) A.map m64AnnulusDomain p))
    {K0 K1 K2 : ℝ} (hK0 : 0 ≤ K0) (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∃ B : M64Annulus (Q.flow.metric (t + h))
          (fun x => c false x (t + h)) (fun x => c true x (t + h)),
        B.area ≤ A.area + h * ((2 * (n : ℝ) - 1) * K0 * A.area + eta) := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  have ht' := Ioo_subset_Icc_self ht
  have hforward := c2_annulus_finite_exists_forward Q.flow c hc ht sigma hsigma A hr
    hminimum hAc hAi hconformal hinj hK0
    (fun p _ => (le_abs_self _).trans
      (auxiliaryCircle_sectional_abs_le_of_ambient_bounds P Q hK0 hBounds ht' (A.map p) _ _))
    (R := ((n : ℝ) - 1) * K0)
    (fun q v => (neg_le_abs _).trans
      (auxiliaryCircle_ricci_quadratic_abs_le_of_unit_bound P Q hn t hK0 q
        (hBounds.riemann t ht' q.1.1) v))
  have hcoef : K0 + 2 * (((n : ℝ) - 1) * K0) = (2 * (n : ℝ) - 1) * K0 := by ring
  simpa only [hcoef] using hforward

end PoincareConjecture.M64
