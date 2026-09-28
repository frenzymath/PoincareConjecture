import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusEnergyDensity
import PoincareConjecture.Proofs.M60.Mathlib.CoordinateEnergyVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation ConjugateVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m64ModulusEnergyDensity_hasDerivAt_of_affine_chart
    (g : RiemannianMetric n M) (r : ℝ) (b : M) (f : LoopPlane → M)
    {U : Set LoopPlane} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ f U)
    (hfU : MapsTo f U (extChartAt (𝓡 n) b).source)
    (V : LoopPlane → EuclideanSpace ℝ (Fin n)) (hV : ContDiff ℝ ∞ V)
    {v : ℝ × LoopPlane → M} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ U))
    (hcoord : ∀ s ∈ Ioo (-epsilon) epsilon, ∀ z ∈ U,
      v (s, z) ∈ (extChartAt (𝓡 n) b).source ∧
        extChartAt (𝓡 n) b (v (s, z)) =
          extChartAt (𝓡 n) b (f z) + s • V z)
    (z : LoopPlane) (hz : z ∈ U) :
    let u := (extChartAt (𝓡 n) b) ∘ f
    let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    HasDerivAt (fun s => m64ModulusEnergyDensity g r (fun p => v (s, p)) z)
      (r * B (u z) (covDerivAlong (christoffelBilinear B) u V (e 0) z)
        (fderiv ℝ u z (e 0)) +
      r⁻¹ * B (u z) (covDerivAlong (christoffelBilinear B) u V (e 1) z)
        (fderiv ℝ u z (e 1))) 0 := by
  let c := extChartAt (𝓡 n) b
  let u := c ∘ f
  let B := g.pullbackCoefficients c.symm
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hu : ContDiffAt ℝ ∞ u z := contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_extChartAt' (n := ∞)
      (by simpa only [extChartAt_source] using hfU hz)).comp z
        (hf.contMDiffAt (hU.mem_nhds hz)))
  have hB : DifferentiableAt ℝ B (u z) :=
    ((g.contDiffOn_chartCoefficients b).contDiffAt
      ((isOpen_extChartAt_target b).mem_nhds (c.map_source (hfU hz)))).differentiableAt
        (by simp)
  have hterm (i : Fin 2) := M60.hasDerivAt_affine_coordinate_energy (u := u) (V := V)
    z (e i) hB (isMetricCompatibleAt_chartCoefficients g b (c.map_source (hfU hz)))
    (fun _ _ => g.symm _ _ _) (christoffelBilinear_chart_symm g b (u z))
  apply (((hterm 0).const_mul r).add ((hterm 1).const_mul r⁻¹)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds
    (show (0 : ℝ) ∈ Ioo (-epsilon) epsilon from ⟨by linarith, hepsilon⟩)] with s hs
  have hvPlane : ContMDiffAt (𝓡 2) (𝓡 n) ∞ (fun p => v (s, p)) z :=
    (hv.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds ⟨hs, hz⟩)).comp z
      (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffAt
  have heq : (fun p => c (v (s, p))) =ᶠ[𝓝 z] (fun p => u p + s • V p) := by
    filter_upwards [hU.mem_nhds hz] with p hp
    exact (hcoord s hs p hp).2
  have hd : HasFDerivAt (fun p => u p + s • V p)
      (fderiv ℝ u z + s • fderiv ℝ V z) z :=
    (hu.differentiableAt (by simp)).hasFDerivAt.add
      ((hV.differentiable (by simp) z).hasFDerivAt.const_smul s)
  unfold m64ModulusEnergyDensity
  rw [m64AreaGram_eq_chart g b (hvPlane.mdifferentiableAt (by simp))
      (hcoord s hs z hz).1 0 0,
    m64AreaGram_eq_chart g b (hvPlane.mdifferentiableAt (by simp))
      (hcoord s hs z hz).1 1 1]
  dsimp only [Function.comp_def]
  rw [heq.fderiv_eq, hd.fderiv, (hcoord s hs z hz).2]
  simp only [add_apply, smul_apply, u, B, e, c, Pi.add_apply, Function.comp_apply]
  ring

end PoincareConjecture
