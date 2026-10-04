import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Cylinder.CylinderChart
import PoincareLib.Geometry.Riemannian.Coordinates.Coefficients

/-!
# The actual spatial metric coefficients of a tracked cylinder

The physical pullback in a birth chart is smooth and positive,
and the cylinder normalization is exactly one scalar factor.
Morgan--Tian, Lemma 16.8 and Proposition 16.5, pp. 372-375;
see derivation 60.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}

/-- Actual physical metric coefficients in a fixed birth chart,
before multiplying by the cylinder's scale. Source: Lemma 16.8,
pp. 372-373; M44 derivation 60. -/
noncomputable def cylinderPhysicalCoefficients
    (e : SurgeryFlowCylinder F C origin scale I U) (f : E → C.carrier)
    (s : ℝ) (hs : s ∈ I) : E → E →L[ℝ] E →L[ℝ] ℝ :=
  (F.metric (origin + s / scale)).pullbackCoefficients (e.forward s hs ∘ f)

/-- Every actual coefficient slice is smooth on any open source
mapping into the tracked region. Source: Lemma 16.8;
M44 derivation 60. -/
theorem cylinderPhysicalCoefficients_smooth
    (e : SurgeryFlowCylinder F C origin scale I U)
    {f : E → C.carrier} {V : Set E} (hV : IsOpen V)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f V) (hmap : MapsTo f V U)
    (s : ℝ) (hs : s ∈ I) :
    ContDiffOn ℝ ∞ (cylinderPhysicalCoefficients e f s hs) V := by
  have hcomp := (e.forward_smooth s hs).comp hf hmap
  intro x hx
  exact ((F.metric (origin + s / scale)).contDiffAt_pullbackCoefficients
    (hcomp.contMDiffAt (hV.mem_nhds hx))).contDiffWithinAt

/-- The composite birth-chart and cylinder differential is
invertible on the actual source. Source: Lemma 16.8;
M44 derivation 60. -/
theorem cylinder_chart_differential_invertible
    (e : SurgeryFlowCylinder F C origin scale I U) (hU : IsOpen U)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞)
    (hmap : f.target ⊆ U) (s : ℝ) (hs : s ∈ I) {x : E} (hx : x ∈ f.source) :
    (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs ∘ f) x).IsInvertible := by
  let d := f.trans (cylinderSliceChart e hU s hs)
  have hxd : x ∈ d.source := ⟨hx, hmap (f.map_source hx)⟩
  have hi := d.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hxd
  exact ⟨hi.mfderivToContinuousLinearEquiv (by simp), rfl⟩

/-- The actual physical coefficients are positive on their open
coordinate source. Source: Lemma 16.8; M44 derivation 60. -/
theorem cylinderPhysicalCoefficients_pos
    (e : SurgeryFlowCylinder F C origin scale I U) (hU : IsOpen U)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞)
    (hmap : f.target ⊆ U) (s : ℝ) (hs : s ∈ I) {x : E} (hx : x ∈ f.source)
    (v : E) (hv : v ≠ 0) : 0 < cylinderPhysicalCoefficients e f s hs x v v := by
  have hi := cylinder_chart_differential_invertible e hU f hmap s hs hx
  apply (F.metric (origin + s / scale)).pos
  intro hz
  apply hv
  apply hi.injective
  rw [map_zero]
  exact hz

/-- Actual metric symmetry is retained in the birth-chart
coefficient field. Source: Lemma 16.8; M44 derivation 60. -/
theorem cylinderPhysicalCoefficients_symm
    (e : SurgeryFlowCylinder F C origin scale I U) (f : E → C.carrier)
    (s : ℝ) (hs : s ∈ I) (x v w : E) :
    cylinderPhysicalCoefficients e f s hs x v w =
      cylinderPhysicalCoefficients e f s hs x w v :=
  (F.metric (origin + s / scale)).symm _ _ _

/-- The normalized coefficient is exactly the frozen cylinder
pullback, with both chart differentials and one scale factor.
Source: Proposition 16.5, p. 370; M44 derivation 60. -/
theorem cylinderPhysicalCoefficients_normalization
    (e : SurgeryFlowCylinder F C origin scale I U) (hU : IsOpen U)
    {f : E → C.carrier} {V : Set E} (hV : IsOpen V)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f V) (hmap : MapsTo f V U)
    (s : ℝ) (hs : s ∈ I) {x : E} (hx : x ∈ V) (v w : E) :
    scale * cylinderPhysicalCoefficients e f s hs x v w =
      e.pullbackInner s hs (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x w) := by
  have hdf := (hf.contMDiffAt (hV.mem_nhds hx)).mdifferentiableAt (by simp)
  have hde := ((e.forward_smooth s hs).contMDiffAt
    (hU.mem_nhds (hmap hx))).mdifferentiableAt (by simp)
  change scale * (F.metric (origin + s / scale)).inner ((e.forward s hs ∘ f) x)
    (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs ∘ f) x v)
    (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs ∘ f) x w) = _
  rw [mfderiv_comp x hde hdf]
  rfl

end PoincareMT.M44
