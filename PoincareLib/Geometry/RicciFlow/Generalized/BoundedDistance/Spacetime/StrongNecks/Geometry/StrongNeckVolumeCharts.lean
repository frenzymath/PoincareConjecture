import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Cylinders.CylinderScalarReadout
import PoincareLib.Geometry.Manifold.InverseFunction.SmoothInverse
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Actual partial coordinate maps for normalized source-neck volume

The chosen sphere chart and axial translation give one fixed model
parametrization. Composition with the actual neck coordinate homeomorphism
retains its precise valid domain and smooth inverse, so the M07 intrinsic
Hausdorff coordinate-volume formula applies to the literal source metric.
Source: Morgan--Tian Definition 2.18, p. 31, and Theorem 5.6, pp. 85-87;
see the cap-topology normalized-neck-volume derivation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M28

open tube

private abbrev E := EuclideanSpace ℝ (Fin 3)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)

local instance : Fact (Module.finrank ℝ E = 2 + 1) := ⟨by simp⟩

private theorem sphere_chart_target (q : UnitTwoSphere) :
    (chartAt E2 q).target = univ := by
  change (stereographic' 2 (-q)).target = univ
  exact stereographic'_target (-q)

/-- The actual fixed model chart used to cover buffered cylinder slabs.
The Euclidean origin represents the literal point `(q,s)`. -/
def neckVolumeModelChart (q : UnitTwoSphere) (s : ℝ) :
    OpenPartialHomeomorph E RoundCylinderSpace :=
  ((cylinderScalarCoordinateEquiv.toHomeomorph.trans
      (Homeomorph.addRight (0, s))).toOpenPartialHomeomorph).trans
    ((chartAt E2 q).symm.prod (OpenPartialHomeomorph.refl ℝ))

/-- The model map is the already fixed sphere inverse and axial translation. -/
theorem neckVolumeModelChart_apply (q : UnitTwoSphere) (s : ℝ) (x : E) :
    neckVolumeModelChart q s x =
      cylinderSphereParametrization q (cylinderScalarCoordinates s x) := rfl

/-- Every Euclidean point is in the actual stereographic model source. -/
theorem neckVolumeModelChart_source (q : UnitTwoSphere) (s : ℝ) :
    (neckVolumeModelChart q s).source = univ := by
  ext x
  change (x ∈ (univ : Set E) ∧
    (cylinderScalarCoordinates s x).1 ∈ (chartAt E2 q).target ∧
    (cylinderScalarCoordinates s x).2 ∈ (univ : Set ℝ)) ↔ x ∈ (univ : Set E)
  simp only [sphere_chart_target, mem_univ, and_self]

/-- The coordinate origin lies over the actual model point, without any
source-neck choice. -/
theorem neckVolumeModelChart_zero (q : UnitTwoSphere) (s : ℝ) :
    neckVolumeModelChart q s 0 = (q, s) := by
  rw [neckVolumeModelChart_apply, cylinderScalarCoordinates_zero]
  change ((chartAt E2 q).symm 0, s) = (q, s)
  rw [← PoincareMT.Proofs.M28.NeckAnalysis.sphere_chart_center q,
    (chartAt E2 q).left_inv (mem_chart_source _ q)]

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

private def neckCoordinateHomeomorph (N : EpsilonNeck g) :
    OpenPartialHomeomorph RoundCylinderSpace M where
  toFun := N.coordinate_map
  invFun := N.coordinate_inverse
  source := univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
  target := N.carrier
  map_source' z hz := N.coordinate_map_mem_of_axial z hz.2
  map_target' x hx := N.coordinate_inverse_mem x hx
  left_inv' z hz := N.coordinate_inverse_coordinate_map_of_axial z hz.2
  right_inv' _ hx := N.coordinate_map_coordinate_inverse hx
  continuousOn_toFun := N.coordinate_map_smooth.continuousOn
  continuousOn_invFun := N.coordinate_inverse_smooth.continuousOn
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := N.carrier_open

/-- The actual neck chart as an open partial homeomorphism, retaining
the original total coordinate map and its literal tested domain. -/
def neckVolumeChart (N : EpsilonNeck g) (q : UnitTwoSphere) (s : ℝ) :
    OpenPartialHomeomorph E M :=
  (neckVolumeModelChart q s).trans (neckCoordinateHomeomorph N)

/-- The volume chart is exactly the existing source coefficient chart. -/
theorem neckVolumeChart_apply (N : EpsilonNeck g) (q : UnitTwoSphere)
    (s : ℝ) (x : E) :
    neckVolumeChart N q s x = cylinderNeckChart N q s x := rfl

/-- The partial chart source is the literal valid neck strip in the fixed
Euclidean parametrization, not a smaller unknown neighborhood. -/
theorem neckVolumeChart_source (N : EpsilonNeck g) (q : UnitTwoSphere) (s : ℝ) :
    (neckVolumeChart N q s).source = cylinderNeckChartDomain N q s := by
  rw [neckVolumeChart, OpenPartialHomeomorph.trans_source,
    neckVolumeModelChart_source, univ_inter]
  ext x
  change (neckVolumeModelChart q s x ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) ↔
    (cylinderScalarCoordinates s x ∈
      (chartAt E2 q).target ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
  rw [neckVolumeModelChart_apply, sphere_chart_target]
  rfl

/-- The literal source chart is smooth on its entire actual open source. -/
theorem neckVolumeChart_smooth (N : EpsilonNeck g) (q : UnitTwoSphere) (s : ℝ) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (neckVolumeChart N q s)
      (neckVolumeChart N q s).source := by
  rw [neckVolumeChart_source]
  exact contMDiffOn_cylinderNeckChart N q s

/-- The actual inverse is smooth on the entire target. The lower inverse
function theorem is applied to the checked invertible chart differential
and its actual local inverse identity. -/
theorem neckVolumeChart_symm_smooth (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (neckVolumeChart N q s).symm
      (neckVolumeChart N q s).target := by
  let e := neckVolumeChart N q s
  intro y hy
  have hx : e.symm y ∈ e.source := e.map_target hy
  have hx' : e.symm y ∈ cylinderNeckChartDomain N q s := by
    simpa only [e, neckVolumeChart_source] using hx
  have hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ e (e.symm y) :=
    (neckVolumeChart_smooth N q s).contMDiffAt (e.open_source.mem_nhds hx)
  have hbij : Function.Bijective (mfderiv (𝓡 3) (𝓡 3) e (e.symm y)) :=
    (cylinderNeckChart_mfderiv_isInvertible N q s hx').bijective
  have hi : ContMDiffAt (𝓡 3) (𝓡 3) ∞ e.symm (e (e.symm y)) := by
    apply Poincare.contMDiffAt_of_local_left_inverse hf hbij
    filter_upwards [e.open_source.mem_nhds hx] with x hx
    exact e.left_inv hx
  rw [e.right_inv hy] at hi
  exact hi.contMDiffWithinAt

end PoincareMT.M28
