import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.ChartMinimalGauss
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.AnnulusStripHarmonic
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.StripLogDensity






noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation

private theorem covDerivAlong_column_smul
    {n : ℕ} {f : LoopPlane → EuclideanSpace ℝ (Fin n)} {p : LoopPlane}
    (hf : ContDiffAt ℝ ∞ f p)
    (Gamma : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (c : ℝ) (d : LoopPlane) :
    covDerivAlong Gamma f (fun q => fderiv ℝ f q (c • d)) (c • d) p =
      c ^ 2 • covDerivAlong Gamma f (fun q => fderiv ℝ f q d) d p := by
  have hV : DifferentiableAt ℝ (fun q => fderiv ℝ f q d) p :=
    ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt
      (by simp)
  have heq : (fun q => fderiv ℝ f q (c • d)) = fun q => c • fderiv ℝ f q d :=
    funext fun q => map_smul _ _ _
  have hd : fderiv ℝ (fun q => c • fderiv ℝ f q d) p =
      c • fderiv ℝ (fun q => fderiv ℝ f q d) p :=
    (hV.hasFDerivAt.fun_const_smul c).fderiv
  rw [covDerivAlong_def, heq, hd, covDerivAlong_def]
  simp only [map_smul, smul_apply, smul_smul, pow_two, smul_add]

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
  {h : RiemannianMetric 2 LoopPlane}




theorem m64Annulus_induced_gaussian_le
    (D : LeviCivitaData g) (Dh : LeviCivitaData h) (A : M64Annulus g c0 c1)
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconf : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hAc : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1})
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusOpenStrip)
    (hinj : ∀ p ∈ m64AnnulusDomain,
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain p))
    {p : LoopPlane} (hp : p ∈ m64AnnulusOpenStrip)
    (hmetric : ∀ᶠ q in 𝓝 p, ∀ u v, h.inner q u v =
      g.inner (A.map q) (mfderiv (𝓡 2) (𝓡 n) A.map q u)
        (mfderiv (𝓡 2) (𝓡 n) A.map q v))
    {K : ℝ} (hsec : ∀ u v, D.sectionalCurvature (A.map p) u v ≤ K) :
    Dh.scalarCurvature p / 2 ≤ K := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let E := r * m60AreaGram g A.map p 0 0
  have hE : 0 < E := mul_pos hr (M64.annulus_strip_gram_pos A hAc hinj hp)
  have hsub : m64AnnulusOpenStrip ⊆ {q : LoopPlane | q 1 ∈ Icc (0 : ℝ) 1} :=
    fun _ hq => ⟨hq.1.le, hq.2.le⟩
  have hclosed := M64.annulus_strip_within_conformal A r hAc
    (hAi.mono (fun _ hq => hq 1 (mem_univ _))) hconf p (hsub hp)
  dsimp only at hclosed
  rw [mfderivWithin_of_mem_nhds
    (mem_of_superset (isOpen_m64AnnulusOpenStrip.mem_nhds hp) hsub)] at hclosed
  have hdiag : E = r⁻¹ * m60AreaGram g A.map p 1 1 := hclosed.1
  have hcross : m60AreaGram g A.map p 0 1 = 0 := hclosed.2
  have hpair (i j : Fin 2) : h.inner p (e i) (e j) = m60AreaGram g A.map p i j :=
    hmetric.self_of_nhds (e i) (e j)
  let a0 := Real.sqrt (r / E)
  let a1 := Real.sqrt (r⁻¹ / E)
  have ha0 : a0 ^ 2 = r / E := Real.sq_sqrt (div_nonneg hr.le hE.le)
  have ha1 : a1 ^ 2 = r⁻¹ / E := Real.sq_sqrt (div_nonneg (inv_nonneg.mpr hr.le) hE.le)
  have hunit0 : h.inner p (a0 • e 0) (a0 • e 0) = 1 := by
    simp only [map_smul, smul_apply, smul_eq_mul, hpair]
    calc
      _ = a0 ^ 2 * m60AreaGram g A.map p 0 0 := by ring
      _ = E / E := by rw [ha0]; dsimp only [E]; ring
      _ = 1 := div_self hE.ne'
  have hunit1 : h.inner p (a1 • e 1) (a1 • e 1) = 1 := by
    simp only [map_smul, smul_apply, smul_eq_mul, hpair]
    calc
      _ = a1 ^ 2 * m60AreaGram g A.map p 1 1 := by ring
      _ = (r⁻¹ * m60AreaGram g A.map p 1 1) / E := by rw [ha1]; ring
      _ = 1 := by rw [← hdiag, div_self hE.ne']
  have horth : h.inner p (a0 • e 0) (a1 • e 1) = 0 := by
    simp only [map_smul, smul_apply, smul_eq_mul, hpair, hcross, mul_zero]
  have hnear : ∀ᶠ q in 𝓝 p, ContMDiffAt (𝓡 2) (𝓡 n) ∞ A.map q := by
    filter_upwards [isOpen_m64AnnulusOpenStrip.mem_nhds hp] with q hq
    exact hAi.contMDiffAt (isOpen_m64AnnulusOpenStrip.mem_nhds hq)
  have hharm := M64.annulus_chart_harmonic_on_strip A hr hminimum hconf hAi
    (A.map p) p hp (mem_extChartAt_source (A.map p))
  have hscaled :
      let c := extChartAt (𝓡 n) (A.map p)
      let f := c ∘ A.map
      let B := g.pullbackCoefficients c.symm
      covDerivAlong (christoffelBilinear B) f (fun q => fderiv ℝ f q (a0 • e 0))
          (a0 • e 0) p +
        covDerivAlong (christoffelBilinear B) f (fun q => fderiv ℝ f q (a1 • e 1))
          (a1 • e 1) p = 0 := by
    dsimp only
    have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (extChartAt (𝓡 n) (A.map p)) (A.map p) :=
      contMDiffAt_extChartAt' (mem_chart_source _ _)
    have hchart := contMDiffAt_iff_contDiffAt.mp (hc.comp p hnear.self_of_nhds)
    rw [covDerivAlong_column_smul hchart, covDerivAlong_column_smul hchart, ha0, ha1]
    have heq := congrArg (fun w : EuclideanSpace ℝ (Fin n) => E⁻¹ • w) hharm
    simpa only [M64.annulusWeightedTension, smul_add, smul_smul, smul_zero,
      div_eq_mul_inv, mul_comm, e] using heq
  exact (m64_harmonic_chart_gaussian_le_sectional D Dh hnear hmetric
    (a0 • e 0) (a1 • e 1) hunit0 hunit1 horth hscaled).trans (hsec _ _)

end PoincareConjecture
