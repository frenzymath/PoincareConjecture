import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingAnnulusFamily
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingAnnulusPeriodicVariation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusBoundaryConormalBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {c0 c1 : ℝ → M}

theorem m64Annulus_exists_forward_competitors_of_curvature_motion
    (F : RicciFlow n M (Icc a b)) {t : ℝ}
    (A : M64Annulus (F.metric t) c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea (F.metric t) c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram (F.metric t) A.map p 0 0 = m60AreaGram (F.metric t) A.map p 1 1 ∧
        m60AreaGram (F.metric t) A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ p ∈ m64AnnulusInterior, (F.connection t).sectionalCurvature (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K)
    (hlower : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 < m60EnergyDensity (F.metric t) A.map (annulusPoint x 0))
    (hupper : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 < m60EnergyDensity (F.metric t) A.map (annulusPoint x 1))
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (f0 f1 : ℝ → ℝ → M)
    (hf0 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q => f0 q.1 q.2) (Ioo (-epsilon) epsilon ×ˢ univ))
    (hf1 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q => f1 q.1 q.2) (Ioo (-epsilon) epsilon ×ˢ univ))
    (hinit0 : ∀ x, f0 0 x = c0 x) (hinit1 : ∀ x, f1 0 x = c1 x)
    (hper0 : ∀ r x, f0 r (x + curvePeriod) = f0 r x)
    (hper1 : ∀ r x, f1 r (x + curvePeriod) = f1 r x)
    (hvelocity0 : ∀ x, curveVelocity (fun r => f0 r x) 0 =
      m62CurvatureVector F (fun y _ => c0 y) t x)
    (hvelocity1 : ∀ x, curveVelocity (fun r => f1 r x) 0 =
      m62CurvatureVector F (fun y _ => c1 y) t x) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∃ B : M64Annulus (F.metric t) (f0 h) (f1 h),
        B.area ≤ A.area + h * (K * A.area + eta) := by
  obtain ⟨delta, hdelta, U, hU, hDU, v, hv, hbase, hperiodic, hlo, hup, hadmit⟩ :=
    m64Annulus_exists_smooth_moving_boundary_family A hO hdom hA hepsilon
      f0 f1 hf0 hf1 hinit0 hinit1 hper0 hper1
  let flux := ∫ x in Icc (0 : ℝ) curvePeriod,
    m64MovingAnnulusCurrent (F.metric t) v 1 (0, annulusPoint x 1) -
      m64MovingAnnulusCurrent (F.metric t) v 1 (0, annulusPoint x 0)
  have hvariation := m64Annulus_periodic_first_variation_of_conformal_minimum
    (F.connection t) A hminimum hconformal hdelta hU hDU hv hbase hperiodic
  have hzero : (0 : ℝ) ∈ Ioo (-delta) delta := ⟨by linarith, hdelta⟩
  have hpoint {x s : ℝ} (hx : x ∈ Icc (0 : ℝ) curvePeriod)
      (hs : s ∈ Icc (0 : ℝ) 1) : annulusPoint x s ∈ m64AnnulusDomain := by
    change 0 ≤ x ∧ x ≤ curvePeriod ∧ 0 ≤ s ∧ s ≤ 1
    exact ⟨hx.1, hx.2, hs⟩
  have hcurrent (x s : ℝ) (hx : x ∈ Icc (0 : ℝ) curvePeriod)
      (hs : s ∈ Icc (0 : ℝ) 1) :
      m64MovingAnnulusCurrent (F.metric t) v 1 (0, annulusPoint x s) =
        (F.metric t).inner (A.map (annulusPoint x s))
          (curveVelocity (fun r => v (r, annulusPoint x s)) 0)
          (curveVelocity (fun r => A.map (annulusPoint x r)) s) := by
    have hmd := (hv.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds
      (show (0, annulusPoint x s) ∈ Ioo (-delta) delta ×ˢ U from
        ⟨hzero, hDU (hpoint hx hs)⟩))).mdifferentiableAt (by simp)
    have hvertical := m64Annulus_vertical_velocity
      ((hA.contMDiffAt (hO.mem_nhds (hdom (hpoint hx hs)))).mdifferentiableAt (by simp))
    rw [m64MovingAnnulusCurrent_eq_pairing (F.metric t) hmd]
    calc
      _ = (F.metric t).inner (A.map (annulusPoint x s))
          (curveVelocity (fun r => v (r, annulusPoint x s)) 0)
          (mfderiv (𝓡 2) (𝓡 n) A.map (annulusPoint x s)
            (EuclideanSpace.basisFun (Fin 2) ℝ 1)) :=
        congrArg (fun f : LoopPlane → M =>
          (F.metric t).inner (f (annulusPoint x s))
            (curveVelocity (fun r => v (r, annulusPoint x s)) 0)
            (mfderiv (𝓡 2) (𝓡 n) f (annulusPoint x s)
              (EuclideanSpace.basisFun (Fin 2) ℝ 1))) (funext hbase)
      _ = _ := by rw [EuclideanSpace.basisFun_apply, ← hvertical]
  have hcurve0 : (fun y (_ : ℝ) => A.map (annulusPoint y 0)) =
      (fun y _ => c0 y) := funext fun y => funext fun _ => A.lower_boundary y
  have hcurve1 : (fun y (_ : ℝ) => A.map (annulusPoint y 1)) =
      (fun y _ => c1 y) := funext fun y => funext fun _ => A.upper_boundary y
  have hbound := m64Annulus_boundary_curvature_flux_le_of_conformal_minimum
    F A hminimum hconformal hO hdom hA hK hsec hlower hupper
  rw [hcurve0, hcurve1] at hbound
  have hfluxle : flux ≤ K * A.area := by
    apply le_trans (le_of_eq ?_) hbound
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [hcurrent x 1 hx (by simp), hcurrent x 0 hx (by simp)]
    have hv0 := congrArg (fun f : ℝ → M => curveVelocity (n := n) f 0)
      (funext (fun r => hlo r x))
    have hv1 := congrArg (fun f : ℝ → M => curveVelocity (n := n) f 0)
      (funext (fun r => hup r x))
    rw [hv0, hv1, hvelocity0, hvelocity1]
  intro eta heta
  have htime : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Ioo (-delta) delta :=
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds hzero)
  filter_upwards [hvariation.2 eta heta, htime, self_mem_nhdsWithin] with h hh ht hpos
  obtain ⟨B, hB⟩ := hadmit h ht (F.metric t)
  refine ⟨B, ?_⟩
  change m64AnnulusArea (F.metric t) B.map ≤ _
  rw [hB]
  apply hh.trans
  change A.area + h * (flux + eta) ≤ _
  nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr hfluxle)]

end PoincareConjecture
