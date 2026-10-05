import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Finite.C2FirstVariation
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Finite.C2CurvatureCurrent
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Finite.RicciBound
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weighted.AnnulusEnergyIdentity

/-! Actual future competitors from a finite-regularity immersed minimum.
The checked first variation and boundary estimate control the literal
moving energy. Each actual motion is admitted as an annulus, and the
proved zero-area collars restore the original boundary labels.
Source: MT Lemma 19.15, pp. 447-449; M64 finite forward derivation. -/

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

/-- An actual closed-C1 immersed conformal minimum supplies literal future competitors with
the boundary-plus-Ricci rate and arbitrary positive slack. No smooth extension across either
boundary is required. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp.
447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem c2_annulus_finite_exists_forward (F : RicciFlow n M (Icc a b))
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
    {K R : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ p ∈ m64AnnulusInterior, (F.connection t).sectionalCurvature (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K)
    (hRic : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      -(F.connection t).ricci q v v ≤ R * (F.metric t).inner q v v) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∃ B : M64Annulus (F.metric (t + h))
          (fun x => c false x (t + h)) (fun x => c true x (t + h)),
        B.area ≤ A.area + h * ((K + 2 * R) * A.area + eta) := by
  have hAd : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map m64AnnulusDomain :=
    hAc.mono (fun _ hp => hp.2.2)
  obtain ⟨epsilon, hepsilon, htime, v, hbase, -, -, -, hvel0, hvel1, hfamily, hder⟩ :=
    m64C2Annulus_exists_finite_first_variation F (hc false) (hc true) ht
      (sigma false) (sigma true) (hsigma false) (hsigma true) A hAd hAi hr hminimum hconformal
  let energy := fun s => ∫ p in m64AnnulusDomain,
    m64ModulusEnergyDensity (F.metric (t + s)) r (v s) p
  let flux := r⁻¹ * ∫ x in Icc (0 : ℝ) curvePeriod,
    m64FiniteAnnulusCurrent (F.metric t) v 1 (annulusPoint x 1) -
      m64FiniteAnnulusCurrent (F.metric t) v 1 (annulusPoint x 0)
  let T := fun p =>
    r * (F.connection t).ricci (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ 0))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) +
    r⁻¹ * (F.connection t).ricci (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
  let d := flux - ∫ p in m64AnnulusDomain, T p
  have hd : HasDerivAt energy d 0 := by
    dsimp only at hder
    rw [show v 0 = A.map from funext hbase] at hder
    exact hder
  have hvelocity (u : Bool) (x : ℝ) :
      curveVelocity (n := n) (fun s => v s (annulusPoint x (if u then 1 else 0))) 0 =
        m62CurvatureVector F (c u) t ((sigma u).map x) := by
    cases u
    · exact hvel0 x
    · exact hvel1 x
  have hflux : flux ≤ K * A.area :=
    (c2_annulus_motion_current_flux_le F c hc ht sigma hsigma A hr hminimum hAc hAi
      hconformal hinj hK hsec v hbase hvelocity).2
  have hR : -(∫ p in m64AnnulusDomain, T p) ≤ 2 * R * A.area :=
    m64Annulus_modulusRicci_neg_integral_le (F.connection t) A hr hAd hconformal hRic
  have hrate : d ≤ (K + 2 * R) * A.area := by
    dsimp only [d]
    nlinarith only [hflux, hR]
  have hcenter : energy 0 = A.area := by
    dsimp only [energy]
    rw [add_zero, show v 0 = A.map from funext hbase]
    exact m64_weightedEnergy_eq_area_of_ae_modulus_conformal A hr hconformal
  have hfuture (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon) :
      ∃ B : M64Annulus (F.metric (t + s))
          (fun x => c false x (t + s)) (fun x => c true x (t + s)),
        B.area ≤ energy s := by
    obtain ⟨B, hmap, -⟩ := hfamily s hs (F.metric (t + s))
    have hB := B.area_le_weightedGramEnergy hr (B.weightedGramEnergy_integrable r)
    have hE : (∫ p in m64AnnulusDomain,
        m64ModulusEnergyDensity (F.metric (t + s)) r B.map p) = energy s :=
      integral_congr_ae (m64ModulusEnergyDensity_ae_eq_of_eqOn (F.metric (t + s)) r hmap)
    obtain ⟨C, hC⟩ := m64C2ShrinkingCurves_freeBoundaryAreaTransport F (hc false) (hc true)
      (Ioo_subset_Icc_self (htime s hs)) (sigma false) (sigma true) B
    exact ⟨C, hC.trans_le (hB.trans_eq hE)⟩
  have hquot : Tendsto (fun h => (energy h - energy 0) / h) (𝓝[>] 0) (𝓝 d) := by
    simpa only [zero_add, smul_eq_mul, ← div_eq_inv_mul] using hd.tendsto_slope_zero_right
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Ioo (-epsilon) epsilon :=
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, hepsilon⟩)
  intro eta heta
  have hevent := hquot.eventually (Iio_mem_nhds (lt_add_of_pos_right d heta))
  filter_upwards [hevent, hsmall, self_mem_nhdsWithin] with h hh hs hpos
  obtain ⟨B, hB⟩ := hfuture h hs
  refine ⟨B, hB.trans ?_⟩
  have hdiff := (div_le_iff₀ hpos).mp hh.le
  rw [hcenter] at hdiff
  have hinc := mul_le_mul_of_nonneg_left hrate hpos.le
  linarith

end PoincareMT.M64
