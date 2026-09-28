import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusFreeCurvatureConormal
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusBranchedBoundaryLimit
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusMinimalBoundaryCurvature
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingAnnulusCurrent














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]





theorem m64MovingAnnulusCurrent_trace_continuous
    (g : RiemannianMetric n M) {v : ℝ × LoopPlane → M}
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {U : Set LoopPlane}
    (hU : IsOpen U) (hDU : m64AnnulusDomain ⊆ U)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ U))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (i : Fin 2) :
    ContinuousOn (fun x => m64MovingAnnulusCurrent g v i (0, annulusPoint x s))
      (Icc (0 : ℝ) curvePeriod) := by
  have hline : Continuous (fun x : ℝ => ((0 : ℝ), annulusPoint x s)) := by
    unfold annulusPoint
    fun_prop
  intro x hx
  have hp : annulusPoint x s ∈ m64AnnulusDomain := ⟨hx.1, hx.2, hs.1, hs.2⟩
  have hreg := hv.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds
    (show (0, annulusPoint x s) ∈ Ioo (-epsilon) epsilon ×ˢ U from
      ⟨⟨by linarith, hepsilon⟩, hDU hp⟩))
  exact ((m64MovingAnnulusCurrent_contDiffAt g hreg i).continuousAt.comp
    (f := fun y : ℝ => ((0 : ℝ), annulusPoint y s)) hline.continuousAt).continuousWithinAt

variable [T2Space M] [CompactSpace M] {a b : ℝ}





theorem m64FreeAnnulus_modulus_log_trace_tendsto_current
    (F : RicciFlow n M (Icc a b)) {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) {t : ℝ} (ht : t ∈ Icc a b)
    {c0 c1 : ℝ → M} (A : M64Annulus (F.metric t) c0 c1)
    {r : ℝ} (hr : 0 < r)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (F.metric t) A.map p 0 0 =
          r⁻¹ * m60AreaGram (F.metric t) A.map p 1 1 ∧
        m60AreaGram (F.metric t) A.map p 0 1 = 0)
    (sigma : M64PeriodicDegreeOneLift) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hboundary : ∀ y, A.map (annulusPoint y s) = c (sigma.map y) t)
    {v : ℝ × LoopPlane → M} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {U : Set LoopPlane} (hU : IsOpen U) (hDU : m64AnnulusDomain ⊆ U)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ U))
    (hbase : ∀ p, v (0, p) = A.map p)
    (hvelocity : ∀ x, curveVelocity (fun z => v (z, annulusPoint x s)) 0 =
      m62CurvatureVector F c t (sigma.map x)) :
    Tendsto (fun m : ℕ => ∫ x in Icc (0 : ℝ) curvePeriod,
      fderiv ℝ (fun q => Real.log
        (m64ModulusEnergyDensity (F.metric t) r A.map q + 1 / ((m : ℝ) + 1)))
        (annulusPoint x s) (EuclideanSpace.single (1 : Fin 2) 1)) atTop
      (𝓝 (-2 * ∫ x in Icc (0 : ℝ) curvePeriod,
        m64MovingAnnulusCurrent (F.metric t) v 1 (0, annulusPoint x s))) := by
  let E := m64ModulusEnergyDensity (F.metric t) r A.map
  let J := fun x => m64MovingAnnulusCurrent (F.metric t) v 1 (0, annulusPoint x s)
  have hE : ContDiffOn ℝ ∞ E O := m64ModulusEnergyDensity_contDiffOn r hO hA
  have hJ : ContinuousOn J (Icc (0 : ℝ) curvePeriod) :=
    m64MovingAnnulusCurrent_trace_continuous (F.metric t) hepsilon hU hDU hv hs 1
  have hfactor (x : ℝ) (hx : x ∈ Icc (0 : ℝ) curvePeriod) :
      E (annulusPoint x s) * J x = -(1 / 2 : ℝ) *
        fderiv ℝ E (annulusPoint x s) (EuclideanSpace.single (1 : Fin 2) 1) ∧
      (E (annulusPoint x s) = 0 → J x = 0) := by
    have hp : annulusPoint x s ∈ m64AnnulusDomain := ⟨hx.1, hx.2, hs.1, hs.2⟩
    have hmd := (hv.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds
      (show (0, annulusPoint x s) ∈ Ioo (-epsilon) epsilon ×ˢ U from
        ⟨⟨by linarith, hepsilon⟩, hDU hp⟩))).mdifferentiableAt (by simp)
    have hvertical := m64Annulus_vertical_velocity
      ((hA.contMDiffAt (hO.mem_nhds (hdom hp))).mdifferentiableAt (by simp))
    have hcurrent : J x = (F.metric t).inner (A.map (annulusPoint x s))
        (m62CurvatureVector F c t (sigma.map x))
        (curveVelocity (fun z => A.map (annulusPoint x z)) s) := by
      rw [show J x = m64MovingAnnulusCurrent (F.metric t) v 1 (0, annulusPoint x s) from rfl,
        m64MovingAnnulusCurrent_eq_pairing (F.metric t) hmd, hvelocity]
      calc
        _ = (F.metric t).inner (A.map (annulusPoint x s))
            (m62CurvatureVector F c t (sigma.map x))
            (mfderiv (𝓡 2) (𝓡 n) A.map (annulusPoint x s)
              (EuclideanSpace.basisFun (Fin 2) ℝ 1)) :=
          congrArg (fun f : LoopPlane → M =>
            (F.metric t).inner (f (annulusPoint x s))
              (m62CurvatureVector F c t (sigma.map x))
              (mfderiv (𝓡 2) (𝓡 n) f (annulusPoint x s)
                (EuclideanSpace.basisFun (Fin 2) ℝ 1))) (funext hbase)
        _ = _ := by rw [EuclideanSpace.basisFun_apply, ← hvertical]
    rw [hcurrent]
    exact m64FreeAnnulus_modulus_boundary_conormal_factor F hc ht A hr hO hdom hA
      hconformal sigma hs hboundary hx
  have hlim := m64Annulus_log_normal_trace_tendsto_of_factored_trace hO hdom hE hs
    (hJ.const_mul (-2)) (fun x _ => m64ModulusEnergyDensity_nonneg r hr.le A.map _)
    (fun x hx => by nlinarith [(hfactor x hx).1])
    (fun x hx he => by rw [(hfactor x hx).2 he, mul_zero])
  simpa only [integral_const_mul] using hlim






theorem m64FreeAnnulus_modulus_curvature_motion_current_flux_le
    (F : RicciFlow n M (Icc a b)) {c0 c1 : ℝ → ℝ → M}
    (hc0 : M63C2ShrinkingCurveOn F c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn F c1 (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (A : M64Annulus (F.metric t)
      ((fun x => c0 x t) ∘ sigma0.map) ((fun x => c1 x t) ∘ sigma1.map))
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (F.metric t)
      ((fun x => c0 x t) ∘ sigma0.map) ((fun x => c1 x t) ∘ sigma1.map))
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (F.metric t) A.map p 0 0 =
          r⁻¹ * m60AreaGram (F.metric t) A.map p 1 1 ∧
        m60AreaGram (F.metric t) A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ p ∈ m64AnnulusInterior, (F.connection t).sectionalCurvature (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K)
    {v : ℝ × LoopPlane → M} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {U : Set LoopPlane} (hU : IsOpen U) (hDU : m64AnnulusDomain ⊆ U)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ U))
    (hbase : ∀ p, v (0, p) = A.map p)
    (hvelocity0 : ∀ x, curveVelocity (fun z => v (z, annulusPoint x 0)) 0 =
      m62CurvatureVector F c0 t (sigma0.map x))
    (hvelocity1 : ∀ x, curveVelocity (fun z => v (z, annulusPoint x 1)) 0 =
      m62CurvatureVector F c1 t (sigma1.map x)) :
    r⁻¹ * (∫ x in Icc (0 : ℝ) curvePeriod,
      m64MovingAnnulusCurrent (F.metric t) v 1 (0, annulusPoint x 1) -
        m64MovingAnnulusCurrent (F.metric t) v 1 (0, annulusPoint x 0)) ≤ K * A.area := by
  let E := m64ModulusEnergyDensity (F.metric t) r A.map
  let b1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  let J := fun s x => m64MovingAnnulusCurrent (F.metric t) v 1 (0, annulusPoint x s)
  have hE : ContDiffOn ℝ ∞ E O := m64ModulusEnergyDensity_contDiffOn r hO hA
  have hlo := m64FreeAnnulus_modulus_log_trace_tendsto_current F hc0 ht A hr
    hO hdom hA hconformal sigma0 (by simp) A.lower_boundary hepsilon hU hDU hv hbase hvelocity0
  have hhi := m64FreeAnnulus_modulus_log_trace_tendsto_current F hc1 ht A hr
    hO hdom hA hconformal sigma1 (by simp) A.upper_boundary hepsilon hU hDU hv hbase hvelocity1
  have hbound : -2 * K * A.area ≤ r⁻¹ *
      ((-2 * ∫ x in Icc (0 : ℝ) curvePeriod, J 1 x) -
        (-2 * ∫ x in Icc (0 : ℝ) curvePeriod, J 0 x)) := by
    apply ge_of_tendsto ((hhi.sub hlo).const_mul r⁻¹)
    apply Eventually.of_forall
    intro m
    let eps : ℝ := 1 / ((m : ℝ) + 1)
    have heps : 0 < eps := by dsimp only [eps]; positivity
    let L := fun p => Real.log (E p + eps)
    have hL : ContDiffOn ℝ ∞ L O := by
      intro p hp
      exact (((hE.contDiffAt (hO.mem_nhds hp)).add contDiffAt_const).log
        (add_pos_of_nonneg_of_pos
          (m64ModulusEnergyDensity_nonneg r hr.le A.map p) heps).ne').contDiffWithinAt
    have hD : ContinuousOn (fun p => fderiv ℝ L p b1) O :=
      ((hL.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn
    have htrace (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        IntegrableOn (fun x => fderiv ℝ L (annulusPoint x s) b1)
          (Icc (0 : ℝ) curvePeriod) volume := by
      have hcurve : Continuous (fun x : ℝ => annulusPoint x s) := by
        unfold annulusPoint
        fun_prop
      apply (hD.comp hcurve.continuousOn ?_).integrableOn_compact isCompact_Icc
      intro x hx
      exact hdom ⟨hx.1, hx.2, hs.1, hs.2⟩
    have hraw := m64Annulus_modulus_log_energy_boundary_lower_bound
      (F.connection t) A hr hminimum hconformal hO hdom hA hK heps hsec
    change -2 * K * A.area ≤ r⁻¹ * ∫ x in Icc (0 : ℝ) curvePeriod,
      fderiv ℝ L (annulusPoint x 1) b1 - fderiv ℝ L (annulusPoint x 0) b1 at hraw
    rw [integral_sub (htrace 1 (by simp)) (htrace 0 (by simp))] at hraw
    exact hraw
  have hi0 : IntegrableOn (J 0) (Icc (0 : ℝ) curvePeriod) volume :=
    (m64MovingAnnulusCurrent_trace_continuous (F.metric t) hepsilon hU hDU hv
      (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1) 1).integrableOn_compact isCompact_Icc
  have hi1 : IntegrableOn (J 1) (Icc (0 : ℝ) curvePeriod) volume :=
    (m64MovingAnnulusCurrent_trace_continuous (F.metric t) hepsilon hU hDU hv
      (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1) 1).integrableOn_compact isCompact_Icc
  change r⁻¹ * (∫ x in Icc (0 : ℝ) curvePeriod, J 1 x - J 0 x) ≤ K * A.area
  rw [integral_sub hi1 hi0]
  nlinarith

end PoincareConjecture
