import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.EnergyDensityCoordinates
import PoincareConjecture.Proofs.M60.Mathlib.CoordinateEnergyVariation










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation ConjugateVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem m60SphereEnergyDensity_hasDerivAt_of_affine_chart
    (g : RiemannianMetric n M) (b : M) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (V : LoopPlane → EuclideanSpace ℝ (Fin n)) (hV : ContDiff ℝ ∞ V)
    {v : ℝ × UnitTwoSphere → M} {ε : ℝ} (hε : 0 < ε)
    (hv : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ v
      (Ioo (-ε) ε ×ˢ (univ : Set UnitTwoSphere)))
    (hcoord : ∀ s ∈ Ioo (-ε) ε, ∀ z : LoopPlane,
      f (m60SphereParameter z) ∈ (extChartAt (𝓡 n) b).source →
        v (s, m60SphereParameter z) ∈ (extChartAt (𝓡 n) b).source ∧
          extChartAt (𝓡 n) b (v (s, m60SphereParameter z)) =
            extChartAt (𝓡 n) b (f (m60SphereParameter z)) + s • V z)
    (z : LoopPlane) (hz : f (m60SphereParameter z) ∈ (extChartAt (𝓡 n) b).source) :
    let u := (extChartAt (𝓡 n) b) ∘ (f ∘ m60SphereParameter)
    let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    HasDerivAt (fun s => m60SphereEnergyDensity g (fun p => v (s, p)) z)
      (∑ i : Fin 2, B (u z)
        (covDerivAlong (christoffelBilinear B) u V (EuclideanSpace.basisFun (Fin 2) ℝ i) z)
        (fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i))) 0 := by
  let φ := f ∘ m60SphereParameter
  let c := extChartAt (𝓡 n) b
  let u := c ∘ φ
  let B := g.pullbackCoefficients c.symm
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let O := φ ⁻¹' c.source
  have hφ : ContMDiff (𝓡 2) (𝓡 n) ∞ φ := hf.comp m60SphereParameter_contMDiff
  have hO : IsOpen O := (isOpen_extChartAt_source b).preimage hφ.continuous
  have hu : ContDiffAt ℝ ∞ u z := contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_extChartAt' (n := ∞)
      (by simpa only [extChartAt_source, φ, Function.comp_apply] using hz)).comp z (hφ z))
  have hB : DifferentiableAt ℝ B (u z) :=
    ((g.contDiffOn_chartCoefficients b).contDiffAt
      ((isOpen_extChartAt_target b).mem_nhds (c.map_source hz))).differentiableAt (by simp)
  have hterm (i : Fin 2) := M60.hasDerivAt_affine_coordinate_energy (u := u) (V := V)
    z (e i) hB (isMetricCompatibleAt_chartCoefficients g b (c.map_source hz))
    (fun _ _ => g.symm _ _ _) (christoffelBilinear_chart_symm g b (u z))
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterm i)
  apply hsum.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨by linarith, hε⟩)]
    with s hs
  have hvPlane : ContMDiff (𝓡 2) (𝓡 n) ∞ (fun y => v (s, m60SphereParameter y)) := by
    intro y
    have hva : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ v
        (s, m60SphereParameter y) := hv.contMDiffAt
          ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs, mem_univ (m60SphereParameter y)⟩)
    exact hva.comp y (contMDiffAt_const.prodMk (m60SphereParameter_contMDiff y))
  have heq : (fun y => c (v (s, m60SphereParameter y))) =ᶠ[𝓝 z]
      (fun y => u y + s • V y) := by
    filter_upwards [hO.mem_nhds hz] with y hy
    exact (hcoord s hs y hy).2
  have hd : HasFDerivAt (fun y => u y + s • V y)
      (fderiv ℝ u z + s • fderiv ℝ V z) z :=
    (hu.differentiableAt (by simp)).hasFDerivAt.add
      ((hV.differentiable (by simp) z).hasFDerivAt.const_smul s)
  change m60EnergyDensity g (fun y => v (s, m60SphereParameter y)) z = _
  rw [m60EnergyDensity_eq_chart g b
    (hvPlane.mdifferentiable (by simp) z) (hcoord s hs z hz).1]
  dsimp only [Function.comp_def]
  rw [heq.fderiv_eq, hd.fderiv, (hcoord s hs z hz).2, Finset.mul_sum]
  rfl

end PoincareConjecture
