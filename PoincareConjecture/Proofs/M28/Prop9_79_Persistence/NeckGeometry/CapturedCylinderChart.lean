import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderScalarReadout
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.CoordinateComposition
import Mathlib.Geometry.Manifold.LocalDiffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.Proofs.M28.NeckTransfer

open PoincareConjecture.M28.tube

variable {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  {h : RiemannianMetric 3 X}

def capturedCylinderMap (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞)
    (N : EpsilonNeck h) (q : UnitTwoSphere) (s : ℝ) :
    EuclideanSpace ℝ (Fin 3) → M :=
  e.symm ∘ cylinderNeckChart N q s

def capturedCylinderCoordinates (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞)
    (N : EpsilonNeck h) (q : UnitTwoSphere) (s : ℝ) (p : M) :
    EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
  (extChartAt (𝓡 3) p) ∘ capturedCylinderMap e N q s

def capturedCylinderChartDomain (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞)
    (N : EpsilonNeck h) (q : UnitTwoSphere) (s : ℝ) (p : M) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  cylinderNeckChartDomain N q s ∩
    (capturedCylinderMap e N q s) ⁻¹' (extChartAt (𝓡 3) p).source

theorem cylinderNeckChart_mem_carrier (N : EpsilonNeck h)
    (q : UnitTwoSphere) (s : ℝ) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ cylinderNeckChartDomain N q s) :
    cylinderNeckChart N q s x ∈ N.carrier :=
  N.coordinate_map_mem_of_axial _ hx.2

omit [IsManifold (𝓡 3) ∞ M] in

theorem capturedCylinderMap_mem_source
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck h)
    (hcapture : N.carrier ⊆ e.target) (q : UnitTwoSphere) (s : ℝ)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ cylinderNeckChartDomain N q s) :
    capturedCylinderMap e N q s x ∈ e.source :=
  e.map_target (hcapture (cylinderNeckChart_mem_carrier N q s hx))

omit [IsManifold (𝓡 3) ∞ M] in

theorem contMDiffOn_capturedCylinderMap
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck h)
    (hcapture : N.carrier ⊆ e.target) (q : UnitTwoSphere) (s : ℝ) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (capturedCylinderMap e N q s)
      (cylinderNeckChartDomain N q s) :=
  e.contMDiffOn_invFun.comp (contMDiffOn_cylinderNeckChart N q s)
    (fun _ hx => hcapture (cylinderNeckChart_mem_carrier N q s hx))

omit [IsManifold (𝓡 3) ∞ M] in

theorem isOpen_capturedCylinderChartDomain
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck h)
    (hcapture : N.carrier ⊆ e.target) (q : UnitTwoSphere) (s : ℝ) (p : M) :
    IsOpen (capturedCylinderChartDomain e N q s p) :=
  (contMDiffOn_capturedCylinderMap e N hcapture q s).continuousOn.isOpen_inter_preimage
    (isOpen_cylinderNeckChartDomain N q s) (isOpen_extChartAt_source p)

omit [IsManifold (𝓡 3) ∞ M] in

theorem zero_mem_capturedCylinderChartDomain
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck h)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (p : M)
    (hp : e.symm (N.coordinate_map (q, s)) ∈ (extChartAt (𝓡 3) p).source) :
    0 ∈ capturedCylinderChartDomain e N q s p := by
  refine ⟨zero_mem_cylinderNeckChartDomain N q hs, ?_⟩
  change e.symm (cylinderNeckChart N q s 0) ∈ (extChartAt (𝓡 3) p).source
  rw [cylinderNeckChart_zero]
  exact hp

theorem contDiffOn_capturedCylinderCoordinates
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck h)
    (hcapture : N.carrier ⊆ e.target) (q : UnitTwoSphere) (s : ℝ) (p : M) :
    ContDiffOn ℝ ∞ (capturedCylinderCoordinates e N q s p)
      (capturedCylinderChartDomain e N q s p) := by
  intro x hx
  have hw := (contMDiffOn_capturedCylinderMap e N hcapture q s).contMDiffAt
    ((isOpen_cylinderNeckChartDomain N q s).mem_nhds hx.1)
  have hc : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (extChartAt (𝓡 3) p)
      (capturedCylinderMap e N q s x) :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source, mem_preimage] using hx.2)
  exact ((hc.comp x hw).contDiffAt).contDiffWithinAt

theorem capturedCylinderCoordinates_source_coefficients
    (gX : RiemannianMetric 3 X)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck h)
    (hcapture : N.carrier ⊆ e.target) (q : UnitTwoSphere) (s : ℝ) (p : M)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ capturedCylinderChartDomain e N q s p) :
    gX.pullbackCoefficients (cylinderNeckChart N q s) x =
      (gX.pullbackCoefficients (e ∘ (extChartAt (𝓡 3) p).symm)
        (capturedCylinderCoordinates e N q s p x)).bilinearComp
          (fderiv ℝ (capturedCylinderCoordinates e N q s p) x)
          (fderiv ℝ (capturedCylinderCoordinates e N q s p) x) := by
  let c := extChartAt (𝓡 3) p
  let w := capturedCylinderMap e N q s
  let psi := capturedCylinderCoordinates e N q s p
  have hU := isOpen_capturedCylinderChartDomain e N hcapture q s p
  have hpsi := (contDiffOn_capturedCylinderCoordinates e N hcapture q s p).contDiffAt
    (hU.mem_nhds hx)
  have hcinv : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm (psi x) :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds (c.map_source hx.2))
  have he : ContMDiffAt (𝓡 3) (𝓡 3) ∞ e (c.symm (psi x)) := by
    have hinv : c.symm (psi x) = w x := c.left_inv hx.2
    rw [hinv]
    exact e.contMDiffOn_toFun.contMDiffAt (e.open_source.mem_nhds
      (capturedCylinderMap_mem_source e N hcapture q s hx.1))
  have heq : (e ∘ c.symm) ∘ psi =ᶠ[𝓝 x] cylinderNeckChart N q s := by
    filter_upwards [hU.mem_nhds hx] with y hy
    change e (c.symm (c (w y))) = cylinderNeckChart N q s y
    rw [c.left_inv hy.2]
    exact e.right_inv (hcapture (cylinderNeckChart_mem_carrier N q s hy.1))
  calc
    gX.pullbackCoefficients (cylinderNeckChart N q s) x =
        gX.pullbackCoefficients ((e ∘ c.symm) ∘ psi) x :=
      (gX.pullbackCoefficients_eq_of_eventuallyEq heq).symm
    _ = _ := gX.pullbackCoefficients_comp
      ((he.comp (psi x) hcinv).mdifferentiableAt (by simp))
      (hpsi.differentiableAt (by simp))

theorem capturedCylinderCoordinates_limit_coefficients
    (g : RiemannianMetric 3 M)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck h)
    (hcapture : N.carrier ⊆ e.target) (q : UnitTwoSphere) (s : ℝ) (p : M)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ capturedCylinderChartDomain e N q s p) :
    g.pullbackCoefficients (capturedCylinderMap e N q s) x =
      (g.pullbackCoefficients (extChartAt (𝓡 3) p).symm
        (capturedCylinderCoordinates e N q s p x)).bilinearComp
          (fderiv ℝ (capturedCylinderCoordinates e N q s p) x)
          (fderiv ℝ (capturedCylinderCoordinates e N q s p) x) := by
  exact g.pullbackCoefficients_eq_chart_pullback p
    ((contMDiffOn_capturedCylinderMap e N hcapture q s).contMDiffAt
      ((isOpen_cylinderNeckChartDomain N q s).mem_nhds hx.1)) hx.2

end PoincareConjecture.Proofs.M28.NeckTransfer
