import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusSliceDifferential












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}






theorem m64Annulus_acceleration_conormal_eq
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    {x s : ℝ} (hp : annulusPoint x s ∈ m64AnnulusDomain) :
    g.inner (A.map (annulusPoint x s))
      (rampHorizontalCovariantDerivative D (fun y => A.map (annulusPoint y s))
        (fun y => curveVelocity (fun z => A.map (annulusPoint z s)) y) x)
      (curveVelocity (fun t => A.map (annulusPoint x t)) s) =
      -(1 / 2 : ℝ) * fderiv ℝ (m60EnergyDensity g A.map) (annulusPoint x s)
        (EuclideanSpace.single (1 : Fin 2) 1) := by
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
  have hconf := m64Annulus_conformal_fderiv_on_domain_of_ae A hO hdom hA hconformal p hp
  have hE : fderiv ℝ (m60EnergyDensity g A.map) p =
      fderiv ℝ (fun q => Q q 0 0) p := by
    have hsum := (hasFDerivAt_const (1 / 2 : ℝ) p).mul
      (((hQ 0 0).differentiableAt (by simp)).hasFDerivAt.add
        ((hQ 1 1).differentiableAt (by simp)).hasFDerivAt)
    have henergy : m60EnergyDensity g A.map = fun q => (1 / 2 : ℝ) *
        (Q q 0 0 + Q q 1 1) := by
      funext q
      exact congrArg (fun r : ℝ => (1 / 2 : ℝ) * r) (Matrix.trace_fin_two (Q q))
    rw [henergy]
    apply hsum.fderiv.trans
    ext v
    have hdiagv := congrArg (fun L : LoopPlane →L[ℝ] ℝ => L v) hconf.1
    simp only [add_apply, smul_apply,
      zero_apply, smul_eq_mul, mul_zero, add_zero]
    change fderiv ℝ (fun q => Q q 0 0) p v =
      fderiv ℝ (fun q => Q q 1 1) p v at hdiagv
    linarith
  have hcross_eq := hcross.unique hcross'
  have hdiag_eq := hdiag.unique hdiag'
  change _ = fderiv ℝ (fun q => Q q 0 1) p b0 at hcross_eq
  rw [hconf.2, zero_apply, ← htor] at hcross_eq
  rw [g.symm] at hdiag_eq
  change _ = -(1 / 2 : ℝ) * fderiv ℝ (m60EnergyDensity g A.map) p b1
  rw [hE]
  linarith

end PoincareConjecture
