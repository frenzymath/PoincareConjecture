import PoincareConjecture.Proofs.M34.Mathlib.RoundCylinderParametrizedJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture.M34

theorem roundCylinderTensorSmoothOn_pullback
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) {ε : ℝ} {f : RoundCylinderSpace → M}
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹)) :
    RoundCylinderTensorSmoothOn ε (roundCylinderPullback g f) := by
  intro q a b x hx
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let U : Set RoundCylinderSpace := univ ×ˢ Ioo (-ε⁻¹) ε⁻¹
  have hU : IsOpen U := isOpen_univ.prod isOpen_Ioo
  have hxU : (c.symm x.1, x.2) ∈ U := ⟨mem_univ _, hx.2⟩
  let φ : RoundCylinderCoordinates → M := fun p => f (c.symm p.1, p.2)
  have hmap : ContMDiffAt 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞ φ x :=
    (hf.contMDiffAt (hU.mem_nhds hxU)).comp x (cylinderChart_symm_smooth q x)
  have hscalar : ContDiffAt ℝ ∞ (fun y => g.parametrizedCoefficients φ y
      (roundCylinderCoordinateBasis a) (roundCylinderCoordinateBasis b)) x :=
    ((g.contDiffAt_parametrizedCoefficients hmap).clm_apply contDiffAt_const).clm_apply
      contDiffAt_const
  have heq : (fun y => roundCylinderTensorCoefficient (roundCylinderPullback g f) c y a b)
      =ᶠ[𝓝 x] (fun y => g.parametrizedCoefficients φ y
        (roundCylinderCoordinateBasis a) (roundCylinderCoordinateBasis b)) := by
    have hnear := (cylinderChart_symm_smooth q).continuous.continuousAt.preimage_mem_nhds
      (hU.mem_nhds hxU)
    filter_upwards [hnear] with y hy
    have h := roundCylinderTensorCoefficient_pullback_eq g q f y
      ((hf.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)) a b
    exact h
  exact (hscalar.congr_of_eventuallyEq heq).contDiffWithinAt

end PoincareConjecture.M34
