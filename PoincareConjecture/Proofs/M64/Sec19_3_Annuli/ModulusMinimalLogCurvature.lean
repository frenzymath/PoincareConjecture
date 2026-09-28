import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusClosedConformality
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusLogRegularization
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusMinimumHarmonic
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.TargetChartEstimate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation ConjugateVariation

private theorem modulus_covDerivAlong_scaled_column
    {n : ℕ} {u : LoopPlane → EuclideanSpace ℝ (Fin n)} {p : LoopPlane}
    (hu : ContDiffAt ℝ ∞ u p)
    (Γ : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) (c : ℝ) (d : LoopPlane) :
    covDerivAlong Γ u (fun q => fderiv ℝ u q (c • d)) (c • d) p =
      c ^ 2 • covDerivAlong Γ u (fun q => fderiv ℝ u q d) d p := by
  have hV : DifferentiableAt ℝ (fun q => fderiv ℝ u q d) p :=
    ((hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt
      (by simp)
  have heq : (fun q => fderiv ℝ u q (c • d)) =
      fun q => c • fderiv ℝ u q d := by
    funext q
    exact map_smul _ _ _
  have hd : fderiv ℝ (fun q => c • fderiv ℝ u q d) p =
      c • fderiv ℝ (fun q => fderiv ℝ u q d) p := by
    exact (hV.hasFDerivAt.fun_const_smul c).fderiv
  rw [covDerivAlong_def, heq, hd, covDerivAlong_def]
  simp only [map_smul, smul_apply, smul_smul, pow_two, smul_add]

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem modulus_sectional_sqrt_scale
    (D : LeviCivitaData g) (x : M) (v w : TangentSpace (𝓡 n) x)
    {r : ℝ} (hr : 0 < r) :
    D.sectionalCurvature x (Real.sqrt r • v) (Real.sqrt r⁻¹ • w) =
      D.sectionalCurvature x v w := by
  have hprod : Real.sqrt r ^ 2 * Real.sqrt r⁻¹ ^ 2 = 1 := by
    rw [Real.sq_sqrt hr.le, Real.sq_sqrt (inv_nonneg.mpr hr.le), mul_inv_cancel₀ hr.ne']
  calc
    _ = (Real.sqrt r ^ 2 * Real.sqrt r⁻¹ ^ 2 * D.curvatureTensor x v w v w) /
        (Real.sqrt r ^ 2 * Real.sqrt r⁻¹ ^ 2 *
          (g.inner x v v * g.inner x w w - g.inner x v w ^ 2)) := by
      unfold LeviCivitaData.sectionalCurvature
      simp only [D.curvatureTensor_smul_first, D.curvatureTensor_smul_second,
        D.curvatureTensor_smul_third, D.curvatureTensor_smul_last,
        map_smul, smul_apply, smul_eq_mul]
      congr 1 <;> ring
    _ = _ := by rw [hprod]; simp only [one_mul]; rfl

variable [T2Space M] [CompactSpace M] {c0 c1 : ℝ → M}

theorem m64Annulus_modulus_log_energy_laplacian_lower_bound
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusInterior)
    {p : LoopPlane} (hp : p ∈ m64AnnulusInterior) {K ε : ℝ}
    (hK : 0 ≤ K) (hε : 0 < ε)
    (hsec : D.sectionalCurvature (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K) :
    -2 * K * m64ModulusEnergyDensity g r A.map p ≤
      r * fderiv ℝ (fun q => fderiv ℝ
          (fun z => Real.log (m64ModulusEnergyDensity g r A.map z + ε)) q
          (EuclideanSpace.single (0 : Fin 2) 1)) p (EuclideanSpace.single (0 : Fin 2) 1) +
        r⁻¹ * fderiv ℝ (fun q => fderiv ℝ
          (fun z => Real.log (m64ModulusEnergyDensity g r A.map z + ε)) q
          (EuclideanSpace.single (1 : Fin 2) 1)) p (EuclideanSpace.single (1 : Fin 2) 1) := by
  let b := A.map p
  let e0 : LoopPlane := EuclideanSpace.single (0 : Fin 2) 1
  let e1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  let d := Real.sqrt r • e0
  let e := Real.sqrt r⁻¹ • e1
  let E := m64ModulusEnergyDensity g r A.map
  let L := fun q => Real.log (E q + ε)
  have hpoint := m64Annulus_modulus_conformal_on_interior_of_ae A r hA hconformal
  have hAp := hA.contMDiffAt (isOpen_m64AnnulusInterior.mem_nhds hp)
  have hchart : ∀ᶠ q in 𝓝 p, A.map q ∈ (extChartAt (𝓡 n) b).source :=
    hAp.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source b).mem_nhds (mem_extChartAt_source b))
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp
    (inter_mem (isOpen_m64AnnulusInterior.mem_nhds hp) hchart)
  have hUI : U ⊆ m64AnnulusInterior := fun q hq => (hUsub hq).1
  have hUchart : MapsTo A.map U (extChartAt (𝓡 n) b).source :=
    fun q hq => (hUsub hq).2
  have hAE : ContDiffOn ℝ ∞ E U :=
    m64ModulusEnergyDensity_contDiffOn r hU (hA.mono hUI)
  have hnonneg (q : LoopPlane) : 0 ≤ E q :=
    m64ModulusEnergyDensity_nonneg r hr.le A.map q
  have henergy (q : LoopPlane) (hq : q ∈ U) :
      E q = r * m60AreaGram g A.map q 0 0 := by
    dsimp only [E, m64ModulusEnergyDensity]
    rw [← (hpoint q (hUI hq)).1]
    ring
  have hdd (q : LoopPlane) (hq : q ∈ U) :
      g.inner (A.map q) (mfderiv (𝓡 2) (𝓡 n) A.map q d)
        (mfderiv (𝓡 2) (𝓡 n) A.map q d) = E q := by
    calc
      _ = Real.sqrt r ^ 2 * m60AreaGram g A.map q 0 0 := by
        simp only [d, e0, m60AreaGram, EuclideanSpace.basisFun_apply,
          map_smul, smul_apply, smul_eq_mul]
        ring
      _ = E q := by rw [Real.sq_sqrt hr.le]; exact (henergy q hq).symm
  have hee (q : LoopPlane) (hq : q ∈ U) :
      g.inner (A.map q) (mfderiv (𝓡 2) (𝓡 n) A.map q e)
        (mfderiv (𝓡 2) (𝓡 n) A.map q e) = E q := by
    calc
      _ = Real.sqrt r⁻¹ ^ 2 * m60AreaGram g A.map q 1 1 := by
        simp only [e, e1, m60AreaGram, EuclideanSpace.basisFun_apply,
          map_smul, smul_apply, smul_eq_mul]
        ring
      _ = E q := by
        rw [Real.sq_sqrt (inv_nonneg.mpr hr.le), ← (hpoint q (hUI hq)).1]
        exact (henergy q hq).symm
  have hde (q : LoopPlane) (hq : q ∈ U) :
      g.inner (A.map q) (mfderiv (𝓡 2) (𝓡 n) A.map q d)
        (mfderiv (𝓡 2) (𝓡 n) A.map q e) = 0 := by
    have hcross := (hpoint q (hUI hq)).2
    simp only [m60AreaGram, EuclideanSpace.basisFun_apply] at hcross
    simp only [d, e, e0, e1, map_smul, smul_apply, smul_eq_mul, hcross, mul_zero]
  have hharm := m64Annulus_chart_harmonic_of_modulus_minimum A hr hminimum hconformal
    b hU hUI (hA.mono hUI) hUchart
  let c := extChartAt (𝓡 n) b
  let u := c ∘ A.map
  let B := g.pullbackCoefficients c.symm
  have hu (q : LoopPlane) (hq : q ∈ U) : ContDiffAt ℝ ∞ u q := by
    have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (A.map q) :=
      contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hUchart hq)
    exact contMDiffAt_iff_contDiffAt.mp
      (hc.comp q (hA.contMDiffAt (isOpen_m64AnnulusInterior.mem_nhds (hUI hq))))
  have hscaled : ∀ q ∈ U,
      covDerivAlong (christoffelBilinear B) u (fun z => fderiv ℝ u z d) d q +
        covDerivAlong (christoffelBilinear B) u (fun z => fderiv ℝ u z e) e q = 0 := by
    intro q hq
    rw [modulus_covDerivAlong_scaled_column (hu q hq),
      modulus_covDerivAlong_scaled_column (hu q hq),
      Real.sq_sqrt hr.le, Real.sq_sqrt (inv_nonneg.mpr hr.le)]
    simpa only [EuclideanSpace.basisFun_apply] using hharm q hq
  have hsec' : D.sectionalCurvature (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p d)
      (mfderiv (𝓡 2) (𝓡 n) A.map p e) ≤ K := by
    simpa only [d, e, map_smul, modulus_sectional_sqrt_scale D (A.map p) _ _ hr] using hsec
  have hraw := m64Modulus_log_add_directional_lower_bound d e hU hpU hAE
    (fun q _ => hnonneg q) hK hε (by
      intro hpa
      have hlocal := m60ConformalHarmonicChart_estimate D b hU hpU d e
        (hA.mono hUI) (fun q hq => hUchart hq) hscaled hdd hee hde hpa
      have hsec'' := hsec'
      unfold LeviCivitaData.sectionalCurvature at hsec''
      rw [hdd p hpU, hee p hpU, hde p hpU, zero_pow (by norm_num), sub_zero] at hsec''
      have hcurv := (div_le_iff₀ (mul_pos hpa hpa)).mp hsec''
      nlinarith)
  have hL : ContDiffAt ℝ 2 L p :=
    (((hAE.contDiffAt (hU.mem_nhds hpU)).add contDiffAt_const).log
      (add_pos_of_nonneg_of_pos (hnonneg p) hε).ne').of_le
        (WithTop.coe_le_coe.mpr le_top)
  change -2 * K * E p ≤
    fderiv ℝ (fun q => fderiv ℝ L q d) p d +
      fderiv ℝ (fun q => fderiv ℝ L q e) p e at hraw
  rw [m64SecondDirectional_smul hL, m64SecondDirectional_smul hL,
    Real.sq_sqrt hr.le, Real.sq_sqrt (inv_nonneg.mpr hr.le)] at hraw
  exact hraw

end PoincareConjecture
