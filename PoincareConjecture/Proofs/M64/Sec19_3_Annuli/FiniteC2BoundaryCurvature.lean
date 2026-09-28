import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.AnnulusBoundaryCurvature
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteRegularBoundaryTrace
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.RelabelAreaRange

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

local notation "S" => Set.ofPred (fun p : LoopPlane => p 1 ∈ Icc (0 : ℝ) 1)

theorem c2_annulus_boundary_curvature_le (F : RicciFlow n M (Icc a b))
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
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K) :
    let C := fun (u : Bool) theta =>
      let p := annulusPoint theta (if u then 1 else 0)
      (F.metric t).inner (A.map p) (m62CurvatureVector F (c u) t ((sigma u).map theta))
        (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain p
          (EuclideanSpace.basisFun (Fin 2) ℝ 1))
    (∀ u, IntegrableOn (C u) (Icc (0 : ℝ) curvePeriod) volume) ∧
      r⁻¹ * (∫ theta in Icc (0 : ℝ) curvePeriod,
        C true theta - C false theta) ≤ K * A.area := by
  classical
  choose d L hd _hperiod hv hL htrace hcurv using
    fun u => m64C2ShrinkingCurve_exists_regular_trace_with_curvature F (hc u) ht
      (sigma u) (hsigma u)
  have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have hmin : A.area = m64LeastAnnulusArea (F.metric t)
      ((fun x => c false x t) ∘ (sigma false).map)
      ((fun x => c true x t) ∘ (sigma true).map) := by
    rw [leastAnnulusArea_comp_lifts_of_C1
      (((hc false).spatial_regular t ht').of_le (by norm_num)) ((hc false).periodic t ht')
      (((hc true).spatial_regular t ht').of_le (by norm_num)) ((hc true).periodic t ht')]
    exact hminimum
  have hboundary (u : Bool) (x : ℝ) :
      A.map (annulusPoint x (if u then 1 else 0)) = d u ((L u).map x) := by
    cases u
    · exact (A.lower_boundary x).trans (htrace false x).symm
    · exact (A.upper_boundary x).trans (htrace true x).symm
  have hbound := annulus_boundary_curvature_le (F.connection t) A hr hmin hAc hAi
    hconformal hinj hK hsec d (fun u => (L u).map) hd hv hL
      (fun u => (L u).monotone) hboundary
  let B := fun (u : Bool) theta =>
    let p := annulusPoint theta (if u then 1 else 0)
    (F.metric t).inner (A.map p) (m62CurvatureVector F (c u) t ((sigma u).map theta))
      (mfderivWithin (𝓡 2) (𝓡 n) A.map S p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
  have hB : (∀ u, IntervalIntegrable (B u) volume 0 curvePeriod) ∧
      r⁻¹ * ((∫ theta in (0 : ℝ)..curvePeriod, B true theta) -
        ∫ theta in (0 : ℝ)..curvePeriod, B false theta) ≤ K * A.area := by
    simpa only [hcurv] using hbound
  let C := fun (u : Bool) theta =>
    let p := annulusPoint theta (if u then 1 else 0)
    (F.metric t).inner (A.map p) (m62CurvatureVector F (c u) t ((sigma u).map theta))
      (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain p
        (EuclideanSpace.basisFun (Fin 2) ℝ 1))
  have hP : (0 : ℝ) ≤ curvePeriod := by unfold curvePeriod; positivity
  have heq (u : Bool) : EqOn (B u) (C u) (Icc (0 : ℝ) curvePeriod) := by
    intro theta hx
    have hp : annulusPoint theta (if u then 1 else 0) ∈ m64AnnulusDomain := by
      refine ⟨hx.1, hx.2, ?_⟩
      cases u <;> norm_num [annulusPoint]
    dsimp only [B, C]
    rw [annulus_within_derivative_restrict hAc hp]
  have hCI (u : Bool) : IntegrableOn (C u) (Icc (0 : ℝ) curvePeriod) volume :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hP).mp (hB.1 u)).congr_fun (heq u)
      measurableSet_Icc
  have hBI (u : Bool) : (∫ theta in (0 : ℝ)..curvePeriod, B u theta) =
      ∫ theta in Icc (0 : ℝ) curvePeriod, C u theta := by
    rw [intervalIntegral.integral_of_le hP, ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_congr_fun measurableSet_Icc (heq u)
  refine ⟨hCI, ?_⟩
  rw [integral_sub (hCI true) (hCI false)]
  simpa only [hBI] using hB.2

end PoincareConjecture.M64
