import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingAnnulusCurrent
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

theorem m64Annulus_curvature_motion_current_flux_le
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
    {v : ℝ × LoopPlane → M} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {U : Set LoopPlane} (hU : IsOpen U) (hDU : m64AnnulusDomain ⊆ U)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ U))
    (hbase : ∀ p, v (0, p) = A.map p)
    (hvelocity0 : ∀ x, curveVelocity (fun r => v (r, annulusPoint x 0)) 0 =
      m62CurvatureVector F (fun y _ => c0 y) t x)
    (hvelocity1 : ∀ x, curveVelocity (fun r => v (r, annulusPoint x 1)) 0 =
      m62CurvatureVector F (fun y _ => c1 y) t x) :
    (∫ x in Icc (0 : ℝ) curvePeriod,
      m64MovingAnnulusCurrent (F.metric t) v 1 (0, annulusPoint x 1) -
        m64MovingAnnulusCurrent (F.metric t) v 1 (0, annulusPoint x 0)) ≤ K * A.area := by
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
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
      (show (0, annulusPoint x s) ∈ Ioo (-epsilon) epsilon ×ˢ U from
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
  apply le_trans (le_of_eq ?_) hbound
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [hcurrent x 1 hx (by simp), hcurrent x 0 hx (by simp), hvelocity0, hvelocity1]

end PoincareConjecture
