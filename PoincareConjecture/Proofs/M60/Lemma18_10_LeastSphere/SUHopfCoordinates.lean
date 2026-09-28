import PoincareConjecture.Proofs.M60.Mathlib.SUHopfCauchyRiemann
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.HarmonicSphereCharts










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation ConjugateVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem m60AreaGram_entry_contDiff (g : RiemannianMetric n M)
    {φ : LoopPlane → M} (hφ : ContMDiff (𝓡 2) (𝓡 n) ∞ φ) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun q => m60AreaGram g φ q i j) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  let c := extChartAt (𝓡 n) (φ p)
  let u := c ∘ φ
  let B := g.pullbackCoefficients c.symm
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (φ p) := contMDiffAt_extChartAt
  have hu : ContDiffAt ℝ ∞ u p :=
    contMDiffAt_iff_contDiffAt.mp (hc.comp p (hφ p))
  have hB : ContDiffAt ℝ ∞ B (u p) :=
    (g.contDiffOn_chartCoefficients (φ p)).contDiffAt
      ((isOpen_extChartAt_target (φ p)).mem_nhds (c.map_source (mem_extChartAt_source _)))
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hdu (k : Fin 2) : ContDiffAt ℝ ∞ (fun q => fderiv ℝ u q (e k)) p :=
    (hu.fderiv_right (by simp)).clm_apply contDiffAt_const
  apply (((hB.comp p hu).clm_apply (hdu i)).clm_apply (hdu j)).congr_of_eventuallyEq
  have hmem : ∀ᶠ q in 𝓝 p, φ q ∈ c.source :=
    (hφ.continuous.continuousAt).preimage_mem_nhds
      ((isOpen_extChartAt_source _).mem_nhds (mem_extChartAt_source _))
  filter_upwards [hmem] with q hq
  have hd (k : Fin 2) : fderiv ℝ u q (e k) = mfderiv (𝓡 n) (𝓡 n) c (φ q)
      (mfderiv (𝓡 2) (𝓡 n) φ q (e k)) := by
    have hh := mfderiv_comp q
      ((contMDiffAt_extChartAt' (x := φ p) (by simpa only [c, extChartAt_source] using hq)
        (n := ∞)).mdifferentiableAt (by simp))
      ((hφ q).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hh
    exact congrArg (fun L => L (e k)) hh
  dsimp only [m60AreaGram]
  rw [hd i, hd j]
  exact (chartCoefficients_apply g (φ p) hq _ _).symm




theorem m60SphereHopf_cauchyRiemann (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hharm : M60SphereChartHarmonic g f) (p : LoopPlane) :
    let G := m60AreaGram g (f ∘ m60SphereParameter)
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    fderiv ℝ (fun q => G q 0 0 - G q 1 1) p (e 0) =
        fderiv ℝ (fun q => -2 * G q 0 1) p (e 1) ∧
      fderiv ℝ (fun q => G q 0 0 - G q 1 1) p (e 1) =
        -fderiv ℝ (fun q => -2 * G q 0 1) p (e 0) := by
  let φ := f ∘ m60SphereParameter
  let c := extChartAt (𝓡 n) (φ p)
  let u := c ∘ φ
  let B := g.pullbackCoefficients c.symm
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hφ : ContMDiff (𝓡 2) (𝓡 n) ∞ φ := hf.comp m60SphereParameter_contMDiff
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (φ p) := contMDiffAt_extChartAt
  have hu : ContDiffAt ℝ ∞ u p :=
    contMDiffAt_iff_contDiffAt.mp (hc.comp p (hφ p))
  have hB : ContDiffAt ℝ ∞ B (u p) :=
    (g.contDiffOn_chartCoefficients (φ p)).contDiffAt
      ((isOpen_extChartAt_target (φ p)).mem_nhds (c.map_source (mem_extChartAt_source _)))
  have hdu (k : Fin 2) : ContDiffAt ℝ ∞ (fun q => fderiv ℝ u q (e k)) p :=
    (hu.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hcompat (v : LoopPlane) (b d : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun q => B (u q) b d) p v =
        B (u p) (christoffelBilinear B (u p) (fderiv ℝ u p v) b) d +
          B (u p) b (christoffelBilinear B (u p) (fderiv ℝ u p v) d) := by
    have hBd := hB.differentiableAt (by simp)
    have hud := hu.differentiableAt (by simp)
    have hd := ((hBd.hasFDerivAt.comp p hud.hasFDerivAt).clm_apply
      (hasFDerivAt_const b p)).clm_apply (hasFDerivAt_const d p)
    dsimp only [Function.comp_def] at hd
    rw [hd.fderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      zero_apply, map_zero, zero_add]
    exact isMetricCompatibleAt_chartCoefficients g (φ p)
      (c.map_source (mem_extChartAt_source _)) _ _ _
  have htor := covDerivAlong_fderiv_symm
    (hu.of_le (WithTop.coe_le_coe.mpr le_top))
    (christoffelBilinear_chart_symm g (φ p) (u p)) (e 0) (e 1)
  have hcr := M60.harmonic_pairing_cauchyRiemann
    (Γ := M60.mapConnectionCoefficients (christoffelBilinear B) u) (e 0) (e 1)
    ((hB.comp p hu).differentiableAt (by simp))
    ((hdu 0).differentiableAt (by simp)) ((hdu 1).differentiableAt (by simp))
    hcompat (fun _ _ => g.symm _ _ _) htor
    (hharm (φ p) p (mem_extChartAt_source _))
  have hmem : ∀ᶠ q in 𝓝 p, φ q ∈ c.source :=
    hφ.continuous.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source _).mem_nhds (mem_extChartAt_source _))
  have hpair (i j : Fin 2) :
      (fun q => B (u q) (fderiv ℝ u q (e i)) (fderiv ℝ u q (e j))) =ᶠ[𝓝 p]
        (fun q => m60AreaGram g φ q i j) := by
    filter_upwards [hmem] with q hq
    have hd (k : Fin 2) : fderiv ℝ u q (e k) = mfderiv (𝓡 n) (𝓡 n) c (φ q)
        (mfderiv (𝓡 2) (𝓡 n) φ q (e k)) := by
      have hh := mfderiv_comp q
        ((contMDiffAt_extChartAt' (x := φ p) (by simpa only [c, extChartAt_source] using hq)
          (n := ∞)).mdifferentiableAt (by simp))
        ((hφ q).mdifferentiableAt (by simp))
      rw [mfderiv_eq_fderiv] at hh
      exact congrArg (fun L => L (e k)) hh
    rw [hd i, hd j]
    exact chartCoefficients_apply g (φ p) hq _ _
  have hA : (fun q => B (u q) (fderiv ℝ u q (e 0)) (fderiv ℝ u q (e 0)) -
      B (u q) (fderiv ℝ u q (e 1)) (fderiv ℝ u q (e 1))) =ᶠ[𝓝 p]
      (fun q => m60AreaGram g φ q 0 0 - m60AreaGram g φ q 1 1) :=
    (hpair 0 0).sub (hpair 1 1)
  have hC : (fun q => -2 * B (u q) (fderiv ℝ u q (e 0)) (fderiv ℝ u q (e 1))) =ᶠ[𝓝 p]
      (fun q => -2 * m60AreaGram g φ q 0 1) :=
    (EventuallyEq.refl _ _).mul (hpair 0 1)
  dsimp only [Function.comp_def] at hcr
  rw [hA.fderiv_eq, hC.fderiv_eq] at hcr
  exact hcr

end PoincareConjecture
