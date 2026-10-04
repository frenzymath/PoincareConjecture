import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Cylinders.CylinderScalarReadout
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.Geometry.CoordinateComposition
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Actual captured cylinder coordinates in a limit chart

The source neck chart is pulled through the guarded stage inverse. Its
composition with a limit chart is smooth on an explicit open domain, and
the source and limit metrics obey the exact coefficient chain rule there.
Source: Morgan--Tian Propositions 9.79 and 10.7, pp. 232-234 and 253;
M28 derivations 103-104.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareMT.Proofs.M28.NeckTransfer

open PoincareMT.M28.tube

variable {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  {h : RiemannianMetric 3 X}

/-- The literal local source neck chart pulled through the stage inverse.
Its meaningful domain is guarded below. Source: M28 derivation 104. -/
def capturedCylinderMap (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞)
    (N : EpsilonNeck h) (q : UnitTwoSphere) (s : ℝ) :
    EuclideanSpace ℝ (Fin 3) → M :=
  e.symm ∘ cylinderNeckChart N q s

/-- Actual Euclidean coordinates of the captured neck in a chosen limit
chart. Source: Proposition 10.7, p. 253; M28 derivation 104. -/
def capturedCylinderCoordinates (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞)
    (N : EpsilonNeck h) (q : UnitTwoSphere) (s : ℝ) (p : M) :
    EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
  (extChartAt (𝓡 3) p) ∘ capturedCylinderMap e N q s

/-- The simultaneous source-neck and target-chart domain. Capture supplies
the remaining stage-inverse guard. Source: M28 derivation 104. -/
def capturedCylinderChartDomain (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞)
    (N : EpsilonNeck h) (q : UnitTwoSphere) (s : ℝ) (p : M) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  cylinderNeckChartDomain N q s ∩
    (capturedCylinderMap e N q s) ⁻¹' (extChartAt (𝓡 3) p).source

/-- The actual cylinder chart lands in the source neck carrier throughout
its valid domain. Source: Proposition 10.7; M28 derivation 104. -/
theorem cylinderNeckChart_mem_carrier (N : EpsilonNeck h)
    (q : UnitTwoSphere) (s : ℝ) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ cylinderNeckChartDomain N q s) :
    cylinderNeckChart N q s x ∈ N.carrier :=
  N.coordinate_map_mem_of_axial _ hx.2

omit [IsManifold (𝓡 3) ∞ M] in
/-- The pulled chart remains in the actual retained stage, so forward and
inverse identities are guarded. Source: M28 derivation 104. -/
theorem capturedCylinderMap_mem_source
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck h)
    (hcapture : N.carrier ⊆ e.target) (q : UnitTwoSphere) (s : ℝ)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ cylinderNeckChartDomain N q s) :
    capturedCylinderMap e N q s x ∈ e.source :=
  e.map_target (hcapture (cylinderNeckChart_mem_carrier N q s hx))

omit [IsManifold (𝓡 3) ∞ M] in
/-- Capture gives smoothness on the whole actual open cylinder-chart
domain, not merely at its origin. Source: M28 derivation 104. -/
theorem contMDiffOn_capturedCylinderMap
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck h)
    (hcapture : N.carrier ⊆ e.target) (q : UnitTwoSphere) (s : ℝ) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (capturedCylinderMap e N q s)
      (cylinderNeckChartDomain N q s) :=
  e.contMDiffOn_invFun.comp (contMDiffOn_cylinderNeckChart N q s)
    (fun _ hx => hcapture (cylinderNeckChart_mem_carrier N q s hx))

omit [IsManifold (𝓡 3) ∞ M] in
/-- The target chart condition cuts out an actual open domain. No common
radius for different charts is needed. Source: M28 derivation 104. -/
theorem isOpen_capturedCylinderChartDomain
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck h)
    (hcapture : N.carrier ⊆ e.target) (q : UnitTwoSphere) (s : ℝ) (p : M) :
    IsOpen (capturedCylinderChartDomain e N q s p) :=
  (contMDiffOn_capturedCylinderMap e N hcapture q s).continuousOn.isOpen_inter_preimage
    (isOpen_cylinderNeckChartDomain N q s) (isOpen_extChartAt_source p)

omit [IsManifold (𝓡 3) ∞ M] in
/-- A valid height and a chart containing the captured neck point put zero
in the actual common domain. Source: Proposition 10.7; derivation 104. -/
theorem zero_mem_capturedCylinderChartDomain
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (N : EpsilonNeck h)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (p : M)
    (hp : e.symm (N.coordinate_map (q, s)) ∈ (extChartAt (𝓡 3) p).source) :
    0 ∈ capturedCylinderChartDomain e N q s p := by
  refine ⟨zero_mem_cylinderNeckChartDomain N q hs, ?_⟩
  change e.symm (cylinderNeckChart N q s 0) ∈ (extChartAt (𝓡 3) p).source
  rw [cylinderNeckChart_zero]
  exact hp

/-- The literal coordinate map is smooth on the common open domain.
Source: Proposition 10.7, p. 253; M28 derivation 104. -/
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

/-- The actual source coefficients equal the atlas coefficients pulled
back by the literal captured coordinate map. Both inverse identities hold
on a neighborhood before differentiating. Source: M28 derivation 104. -/
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

/-- The limit metric is pulled back by exactly the same captured
coordinate map as the source metric. Source: M28 derivation 104. -/
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

end PoincareMT.Proofs.M28.NeckTransfer
