import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusClosedConformality
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusCurvatureConormal













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}





theorem m64Annulus_modulus_acceleration_conormal_eq
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1) (r : ℝ)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    {x s : ℝ} (hp : annulusPoint x s ∈ m64AnnulusDomain) :
    r * g.inner (A.map (annulusPoint x s))
      (rampHorizontalCovariantDerivative D (fun y => A.map (annulusPoint y s))
        (fun y => curveVelocity (fun z => A.map (annulusPoint z s)) y) x)
      (curveVelocity (fun t => A.map (annulusPoint x t)) s) =
      -(1 / 2 : ℝ) * fderiv ℝ (m64ModulusEnergyDensity g r A.map)
        (annulusPoint x s) (EuclideanSpace.single (1 : Fin 2) 1) := by
  let c := fun y t => A.map (annulusPoint y t)
  let p := annulusPoint x s
  let b0 : LoopPlane := EuclideanSpace.single (0 : Fin 2) 1
  let b1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  let Q := m60AreaGram g A.map
  have hAp := hA.contMDiffAt (hO.mem_nhds (hdom hp))
  have hxline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun y : ℝ => (y, s)) x :=
    contMDiffAt_iff_contDiffAt.mpr (contDiffAt_id.prodMk contDiffAt_const)
  have hsline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun t : ℝ => (x, t)) s :=
    contMDiffAt_iff_contDiffAt.mpr (contDiffAt_const.prodMk contDiffAt_id)
  have hX := m64Annulus_horizontal_velocity_contMDiffAt hO hA
    (q := (x, s)) (hdom hp)
  have hZ := m64Annulus_vertical_velocity_contMDiffAt hO hA
    (q := (x, s)) (hdom hp)
  have hcx : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun y => c y s) x :=
    (hAp.mdifferentiableAt (by simp)).comp x
      (m64AnnulusPoint_horizontal_hasDerivAt s x).differentiableAt.mdifferentiableAt
  have hcs : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (c x) s :=
    (hAp.mdifferentiableAt (by simp)).comp s
      (m64AnnulusPoint_vertical_hasDerivAt x s).differentiableAt.mdifferentiableAt
  have hcross := M62.hasDerivAt_metric_pairing D hcx
    ((hX.comp x hxline).mdifferentiableAt (by simp))
    ((hZ.comp x hxline).mdifferentiableAt (by simp))
  have hdiag := M62.hasDerivAt_metric_pairing D hcs
    ((hX.comp s hsline).mdifferentiableAt (by simp))
    ((hX.comp s hsline).mdifferentiableAt (by simp))
  have hQ (i j : Fin 2) : ContDiffAt ℝ ∞ (fun q => Q q i j) p :=
    m64AreaGram_entry_contDiffAt (g := g) hAp i j
  have hcross' : HasDerivAt
      (fun y => g.inner (c y s) (curveVelocity (fun z => c z s) y)
        (curveVelocity (c y) s)) (fderiv ℝ (fun q => Q q 0 1) p b0) x := by
    have h := ((hQ 0 1).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt x
      (m64AnnulusPoint_horizontal_hasDerivAt s x)
    apply h.congr_of_eventuallyEq
    have hnear := (m64AnnulusPoint_horizontal_hasDerivAt s x).continuousAt
      (hO.mem_nhds (hdom hp))
    filter_upwards [hnear] with y hy
    have hfy := (hA.contMDiffAt (hO.mem_nhds hy)).mdifferentiableAt (by simp)
    dsimp only [c, Q]
    rw [m64Annulus_horizontal_velocity hfy, m64Annulus_vertical_velocity hfy]
    simp only [Function.comp_def, m60AreaGram, EuclideanSpace.basisFun_apply]
  have hdiag' : HasDerivAt
      (fun t => g.inner (c x t) (curveVelocity (fun y => c y t) x)
        (curveVelocity (fun y => c y t) x))
      (fderiv ℝ (fun q => Q q 0 0) p b1) s := by
    have h := ((hQ 0 0).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s
      (m64AnnulusPoint_vertical_hasDerivAt x s)
    apply h.congr_of_eventuallyEq
    have hnear := (m64AnnulusPoint_vertical_hasDerivAt x s).continuousAt
      (hO.mem_nhds (hdom hp))
    filter_upwards [hnear] with t ht
    have hft := (hA.contMDiffAt (hO.mem_nhds ht)).mdifferentiableAt (by simp)
    dsimp only [c, Q]
    rw [m64Annulus_horizontal_velocity hft]
    simp only [Function.comp_def, m60AreaGram, EuclideanSpace.basisFun_apply]
  have hP : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞
      (fun z : ℝ × ℝ => annulusPoint z.1 z.2) := by
    apply contMDiff_iff_contDiff.mpr
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · simpa [annulusPoint] using (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : ℝ × ℝ → ℝ))
    · simpa [annulusPoint] using (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × ℝ → ℝ))
  let Omega := (fun z : ℝ × ℝ => annulusPoint z.1 z.2) ⁻¹' O
  have hOmega : IsOpen Omega := hO.preimage hP.continuous
  have hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun z : ℝ × ℝ => c z.1 z.2) Omega :=
    hA.comp hP.contMDiffOn (fun _ hz => hz)
  have htor := M62.pullback_velocity_commute D c hOmega hc (hdom hp)
  have hconf := m64Annulus_modulus_conformal_fderiv_on_domain_of_ae
    A r hO hdom hA hconformal p hp
  have hE : fderiv ℝ (m64ModulusEnergyDensity g r A.map) p b1 =
      r * fderiv ℝ (fun q => Q q 0 0) p b1 := by
    rw [hconf.1, (((hQ 0 0).differentiableAt (by simp)).hasFDerivAt.const_mul r).fderiv]
    rfl
  have hcross_eq := hcross.unique hcross'
  have hdiag_eq := hdiag.unique hdiag'
  change _ = fderiv ℝ (fun q => Q q 0 1) p b0 at hcross_eq
  rw [hconf.2, zero_apply, ← htor] at hcross_eq
  rw [g.symm] at hdiag_eq
  change r * _ = -(1 / 2 : ℝ) *
    fderiv ℝ (m64ModulusEnergyDensity g r A.map) p b1
  rw [hE]
  calc
    r * _ = r * (-(1 / 2 : ℝ) * fderiv ℝ (fun q => Q q 0 0) p b1) :=
      congrArg (fun z : ℝ => r * z) (by linarith only [hcross_eq, hdiag_eq])
    _ = _ := by ring

variable {a b : ℝ}





theorem m64Annulus_modulus_curvature_conormal_eq
    (F : RicciFlow n M (Icc a b)) {t : ℝ}
    (A : M64Annulus (F.metric t) c0 c1) {r : ℝ} (hr : 0 < r)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (F.metric t) A.map p 0 0 =
          r⁻¹ * m60AreaGram (F.metric t) A.map p 1 1 ∧
        m60AreaGram (F.metric t) A.map p 0 1 = 0)
    {x s : ℝ} (hp : annulusPoint x s ∈ m64AnnulusDomain)
    (hpos : 0 < m64ModulusEnergyDensity (F.metric t) r A.map (annulusPoint x s)) :
    (F.metric t).inner (A.map (annulusPoint x s))
      (m62CurvatureVector F (fun y _ => A.map (annulusPoint y s)) t x)
      (curveVelocity (fun z => A.map (annulusPoint x z)) s) =
      -(1 / 2 : ℝ) *
        (fderiv ℝ (m64ModulusEnergyDensity (F.metric t) r A.map) (annulusPoint x s)
          (EuclideanSpace.single (1 : Fin 2) 1) /
            m64ModulusEnergyDensity (F.metric t) r A.map (annulusPoint x s)) := by
  let q := fun y (_ : ℝ) => A.map (annulusPoint y s)
  let E := m64ModulusEnergyDensity (F.metric t) r A.map
  let p := annulusPoint x s
  let Q := m60AreaGram (F.metric t) A.map p 0 0
  let Y := curveVelocity (n := n) (fun y => q y t) x
  let Z := curveVelocity (n := n) (fun z => A.map (annulusPoint x z)) s
  have hAp := hA.contMDiffAt (hO.mem_nhds (hdom hp))
  have hdiff := hAp.mdifferentiableAt (by simp)
  have hconf := m64Annulus_modulus_conformal_on_domain_of_ae A r hO hdom hA hconformal p hp
  have henergy : E p = r * Q := by
    dsimp only [E, m64ModulusEnergyDensity, Q]
    rw [← hconf.1]
    ring
  have hQpos : 0 < Q := by nlinarith [henergy]
  have hpair : (F.metric t).inner (q x t) Y Y = Q := by
    dsimp only [Y, q, Q, p]
    rw [m64Annulus_horizontal_velocity hdiff]
    simp only [m60AreaGram, EuclideanSpace.basisFun_apply]
  have horth : (F.metric t).inner (q x t) Y Z = 0 := by
    change (F.metric t).inner (A.map p)
      (curveVelocity (fun y => A.map (annulusPoint y s)) x)
      (curveVelocity (fun z => A.map (annulusPoint x z)) s) = 0
    rw [m64Annulus_horizontal_velocity hdiff, m64Annulus_vertical_velocity hdiff]
    simpa only [m60AreaGram, EuclideanSpace.basisFun_apply] using hconf.2
  have hsq : curveSpeed F q t x ^ 2 = Q := (M62.speed_sq F q t x).trans hpair
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
    exact hQpos.ne'
  have hcurv := M63.curvatureVector_eq_acceleration_sub_tangent F q hX
    hv.hasDerivAt hspeed.ne'
  have hacc := m64Annulus_modulus_acceleration_conormal_eq (F.connection t) A r
    hO hdom hA hconformal hp
  change (F.metric t).inner (q x t) (m62CurvatureVector F q t x) Z = _
  rw [hcurv]
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
  change (curveSpeed F q t x ^ 2)⁻¹ *
      (F.metric t).inner (A.map p)
        (rampHorizontalCovariantDerivative (F.connection t) (fun y => A.map (annulusPoint y s))
          (fun y => curveVelocity (fun z => A.map (annulusPoint z s)) y) x)
        (curveVelocity (fun z => A.map (annulusPoint x z)) s) -
      (deriv (curveSpeed F q t) x / curveSpeed F q t x ^ 3) *
        (F.metric t).inner (q x t) Y Z = _
  rw [horth, mul_zero, sub_zero, hsq]
  change Q⁻¹ * _ = -(1 / 2 : ℝ) *
    (fderiv ℝ E p (EuclideanSpace.single (1 : Fin 2) 1) / E p)
  rw [henergy]
  field_simp [hr.ne', hQpos.ne']
  nlinarith [hacc]

end PoincareConjecture
