import PoincareConjecture.Proofs.M35.Thm12_28.CylinderCharts
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem roundCylinderPullback_coefficient_eq_euclidean
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (coordinate : RoundCylinderSpace → M)
    (q : UnitTwoSphere) (p : E3) (a b : Fin 3)
    (hc : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate (cylinderChart q p)) :
    g.pullbackCoefficients (coordinate ∘ cylinderChart q) p
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) =
      roundCylinderTensorCoefficient (roundCylinderPullback g coordinate)
        (chartAt E2 q) (cylinderCoordinateEquiv p) a b := by
  have hcomp := mfderiv_comp p (hc.mdifferentiableAt (by simp))
    ((cylinderChart_contMDiff q p).mdifferentiableAt (by simp))
  have hv (i : Fin 3) :
      mfderiv (𝓡 3) (𝓡 3) (coordinate ∘ cylinderChart q) p
        (EuclideanSpace.basisFun (Fin 3) ℝ i) =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate (cylinderChart q p)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E2 q).symm (cylinderCoordinateEquiv p).1
          (roundCylinderCoordinateBasis i).1, (roundCylinderCoordinateBasis i).2) := by
    have hchart := mfderiv_cylinderChart q p (EuclideanSpace.basisFun (Fin 3) ℝ i)
    rw [cylinderCoordinateEquiv_basis] at hchart
    exact (congrArg (fun L => L (EuclideanSpace.basisFun (Fin 3) ℝ i)) hcomp).trans
      (congrArg (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate
        (cylinderChart q p)) hchart)
  exact congrArg₂ (fun v w => g.inner (coordinate (cylinderChart q p)) v w) (hv a) (hv b)

theorem roundCylinderPullback_coefficient_contDiffAt
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (coordinate : RoundCylinderSpace → M)
    {U : Set RoundCylinderSpace} (hU : IsOpen U)
    (hc : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate U)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates)
    (hp : ((chartAt E2 q).symm p.1, p.2) ∈ U) (a b : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => roundCylinderTensorCoefficient
      (roundCylinderPullback g coordinate) (chartAt E2 q) y a b) p := by
  have hdom : cylinderChart q (cylinderCoordinateEquiv.symm p) ∈ U := by
    simpa only [cylinderChart, ContinuousLinearEquiv.apply_symm_apply] using hp
  have hparam := (hc.contMDiffAt (hU.mem_nhds hdom)).comp
    (cylinderCoordinateEquiv.symm p) (cylinderChart_contMDiff q _)
  have hg := g.contDiffAt_pullbackCoefficients hparam
  have ha := hg.clm_apply (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 3) ℝ a))
  have hab := ha.clm_apply (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 3) ℝ b))
  apply (hab.comp p cylinderCoordinateEquiv.symm.contDiff.contDiffAt).congr_of_eventuallyEq
  have hnear := (preferredCylinderChart_contMDiff q p).continuousAt.preimage_mem_nhds
    (hU.mem_nhds hp)
  filter_upwards [hnear] with y hy
  have hdy : cylinderChart q (cylinderCoordinateEquiv.symm y) ∈ U := by
    simpa only [cylinderChart, ContinuousLinearEquiv.apply_symm_apply, mem_preimage] using hy
  simpa only [ContinuousLinearEquiv.apply_symm_apply, Function.comp_apply] using
    (roundCylinderPullback_coefficient_eq_euclidean g coordinate q
      (cylinderCoordinateEquiv.symm y) a b (hc.contMDiffAt (hU.mem_nhds hdy))).symm

theorem roundCylinderPullback_scaled_smoothOn
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (coordinate : RoundCylinderSpace → M)
    (epsilon Q : ℝ)
    (hc : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate
      (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹)) :
    RoundCylinderTensorSmoothOn epsilon
      (fun z v w => Q * roundCylinderPullback g coordinate z v w) := by
  intro q a b p hp
  have hs := roundCylinderPullback_coefficient_contDiffAt g coordinate
    (isOpen_univ.prod isOpen_Ioo) hc q p ⟨mem_univ _, hp.2⟩ a b
  exact ((contDiffAt_const (c := Q)).mul hs).contDiffWithinAt

end PoincareConjecture.M35
