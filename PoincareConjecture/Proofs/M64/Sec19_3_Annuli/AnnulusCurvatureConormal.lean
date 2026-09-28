import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusConormalAcceleration
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ParabolicGaugeGeometry
import PoincareConjecture.Proofs.M62.Lemma0_1_Speed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {c0 c1 : ℝ → M}

theorem m64Annulus_curvature_conormal_eq
    (F : RicciFlow n M (Icc a b)) {t : ℝ}
    (A : M64Annulus (F.metric t) c0 c1)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram (F.metric t) A.map p 0 0 = m60AreaGram (F.metric t) A.map p 1 1 ∧
        m60AreaGram (F.metric t) A.map p 0 1 = 0)
    {x s : ℝ} (hp : annulusPoint x s ∈ m64AnnulusDomain)
    (hpos : 0 < m60EnergyDensity (F.metric t) A.map (annulusPoint x s)) :
    (F.metric t).inner (A.map (annulusPoint x s))
      (m62CurvatureVector F (fun y _ => A.map (annulusPoint y s)) t x)
      (curveVelocity (fun r => A.map (annulusPoint x r)) s) =
      -(1 / 2 : ℝ) *
        (fderiv ℝ (m60EnergyDensity (F.metric t) A.map) (annulusPoint x s)
          (EuclideanSpace.single (1 : Fin 2) 1) /
            m60EnergyDensity (F.metric t) A.map (annulusPoint x s)) := by
  let q := fun y (_ : ℝ) => A.map (annulusPoint y s)
  let E := m60EnergyDensity (F.metric t) A.map
  let p := annulusPoint x s
  let Y := curveVelocity (n := n) (fun y => q y t) x
  let Z := curveVelocity (n := n) (fun r => A.map (annulusPoint x r)) s
  have hAp := hA.contMDiffAt (hO.mem_nhds (hdom hp))
  have hdiff := hAp.mdifferentiableAt (by simp)
  have hconf := m64Annulus_conformal_on_domain_of_ae A hO hdom hA hconformal p hp
  have henergy : E p = m60AreaGram (F.metric t) A.map p 0 0 := by
    change (1 / 2 : ℝ) * Matrix.trace (m60AreaGram (F.metric t) A.map p) = _
    rw [Matrix.trace_fin_two, ← hconf.1]
    ring
  have hpair : (F.metric t).inner (q x t) Y Y = E p := by
    rw [henergy]
    dsimp only [Y, q, p]
    rw [m64Annulus_horizontal_velocity hdiff]
    simp only [m60AreaGram, EuclideanSpace.basisFun_apply]
  have horth : (F.metric t).inner (q x t) Y Z = 0 := by
    change (F.metric t).inner (A.map p)
      (curveVelocity (fun y => A.map (annulusPoint y s)) x)
      (curveVelocity (fun r => A.map (annulusPoint x r)) s) = 0
    rw [m64Annulus_horizontal_velocity hdiff, m64Annulus_vertical_velocity hdiff]
    simpa only [m60AreaGram, EuclideanSpace.basisFun_apply] using hconf.2
  have hsq : curveSpeed F q t x ^ 2 = E p := (M62.speed_sq F q t x).trans hpair
  have hspeed : 0 < curveSpeed F q t x := by
    have hn := M62.speed_nonneg F q t x
    nlinarith
  have hxline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun y : ℝ => (y, s)) x :=
    contMDiffAt_iff_contDiffAt.mpr (contDiffAt_id.prodMk contDiffAt_const)
  have hX := ((m64Annulus_horizontal_velocity_contMDiffAt hO hA
    (q := (x, s)) (hdom hp)).comp x hxline).mdifferentiableAt (by simp)
  have hcx : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun y => q y t) x :=
    hdiff.comp x
      (m64AnnulusPoint_horizontal_hasDerivAt s x).differentiableAt.mdifferentiableAt
  have hmetric := M62.hasDerivAt_metric_pairing (F.connection t) hcx hX hX
  have hv : DifferentiableAt ℝ (curveSpeed F q t) x := by
    change DifferentiableAt ℝ (fun y => Real.sqrt
      ((F.metric t).inner (q y t) (curveVelocity (fun z => q z t) y)
        (curveVelocity (fun z => q z t) y))) x
    apply hmetric.differentiableAt.sqrt
    change (F.metric t).inner (q x t) Y Y ≠ 0
    rw [hpair]
    exact hpos.ne'
  have hcurv := M63.curvatureVector_eq_acceleration_sub_tangent F q hX
    hv.hasDerivAt hspeed.ne'
  have hacc := m64Annulus_acceleration_conormal_eq (F.connection t) A
    hO hdom hA hconformal hp
  change (F.metric t).inner (q x t) (m62CurvatureVector F q t x) Z = _
  rw [hcurv]
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
  change (curveSpeed F q t x ^ 2)⁻¹ *
      (F.metric t).inner (A.map p)
        (rampHorizontalCovariantDerivative (F.connection t) (fun y => A.map (annulusPoint y s))
          (fun y => curveVelocity (fun z => A.map (annulusPoint z s)) y) x)
        (curveVelocity (fun r => A.map (annulusPoint x r)) s) -
      (deriv (curveSpeed F q t) x / curveSpeed F q t x ^ 3) *
        (F.metric t).inner (q x t) Y Z = _
  rw [hacc, horth, mul_zero, sub_zero, hsq]
  change (E p)⁻¹ * (-(1 / 2 : ℝ) *
    fderiv ℝ E p (EuclideanSpace.single (1 : Fin 2) 1)) = _
  ring

end PoincareConjecture
