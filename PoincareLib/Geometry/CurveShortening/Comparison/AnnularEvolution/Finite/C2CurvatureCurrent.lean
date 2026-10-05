import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Finite.C2BoundaryCurvature
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Finite.CurrentTraces

/-! The actual moving annulus has the original curvature-current bound.
Only its base map and the two genuine boundary velocities are needed
to identify the already bounded original curvature-conormal term.
Source: MT Lemma 19.15, pp. 447-449; M64 truncated curvature derivation. -/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareMT.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

local notation "S" => Set.ofPred (fun p : LoopPlane => p 1 ∈ Icc (0 : ℝ) 1)

/-- The boundary current of the actual finite-regularity motion has the sectional-area
bound, with its original labels and both orientations. Source: Morgan--Tian (2007), Lemma
19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem c2_annulus_motion_current_flux_le (F : RicciFlow n M (Icc a b))
    (c : Bool → ℝ → ℝ → M) (hc : ∀ u, M63C2ShrinkingCurveOn F (c u) (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (sigma : Bool → M64PeriodicDegreeOneLift)
    (hsigma : ∀ u, ContDiff ℝ 1 (sigma u).map)
    (A : M64Annulus (F.metric t)
      ((fun x => c false x t) ∘ (sigma false).map)
      ((fun x => c true x t) ∘ (sigma true).map))
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (F.metric t)
      (fun x => c false x t) (fun x => c true x t))
    (hAc : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S)
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusOpenStrip)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (F.metric t) A.map p 0 0 =
        r⁻¹ * m60AreaGram (F.metric t) A.map p 1 1 ∧
      m60AreaGram (F.metric t) A.map p 0 1 = 0)
    (hinj : ∀ p ∈ m64AnnulusDomain,
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain p))
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ p ∈ m64AnnulusInterior, (F.connection t).sectionalCurvature (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K)
    (v : ℝ → LoopPlane → M) (hbase : ∀ p, v 0 p = A.map p)
    (hvelocity : ∀ (u : Bool) x,
      curveVelocity (n := n) (fun s => v s (annulusPoint x (if u then 1 else 0))) 0 =
        m62CurvatureVector F (c u) t ((sigma u).map x)) :
    (∀ u : Bool, IntegrableOn
      (fun x => m64FiniteAnnulusCurrent (F.metric t) v 1 (annulusPoint x (if u then 1 else 0)))
      (Icc (0 : ℝ) curvePeriod) volume) ∧
    r⁻¹ * (∫ x in Icc (0 : ℝ) curvePeriod,
      m64FiniteAnnulusCurrent (F.metric t) v 1 (annulusPoint x 1) -
        m64FiniteAnnulusCurrent (F.metric t) v 1 (annulusPoint x 0)) ≤ K * A.area := by
  have hbound := c2_annulus_boundary_curvature_le F c hc ht sigma hsigma A hr hminimum
    hAc hAi hconformal hinj hK hsec
  have heq (u : Bool) (x : ℝ) :
      m64FiniteAnnulusCurrent (F.metric t) v 1 (annulusPoint x (if u then 1 else 0)) =
      (F.metric t).inner (A.map (annulusPoint x (if u then 1 else 0)))
        (m62CurvatureVector F (c u) t ((sigma u).map x))
        (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain
          (annulusPoint x (if u then 1 else 0)) (EuclideanSpace.basisFun (Fin 2) ℝ 1)) := by
    rw [m64FiniteAnnulusCurrent, hvelocity u x, funext hbase]
  constructor
  · intro u
    simpa only [heq u] using hbound.1 u
  · have hupper := heq true
    have hlower := heq false
    simp only [Bool.false_eq_true, if_false, if_true] at hupper hlower hbound
    simpa only [hupper, hlower] using hbound.2

end PoincareMT.M64
