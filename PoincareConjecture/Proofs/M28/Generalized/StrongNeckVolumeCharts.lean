import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderScalarReadout
import PoincareConjecture.Proofs.M07.Geometry.Manifold.InverseFunction.SmoothInverse
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

open tube

private abbrev E := EuclideanSpace ℝ (Fin 3)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)

local instance : Fact (Module.finrank ℝ E = 2 + 1) := ⟨by simp⟩

private theorem sphere_chart_target (q : UnitTwoSphere) :
    (chartAt E2 q).target = univ := by
  change (stereographic' 2 (-q)).target = univ
  exact stereographic'_target (-q)

def neckVolumeModelChart (q : UnitTwoSphere) (s : ℝ) :
    OpenPartialHomeomorph E RoundCylinderSpace :=
  ((cylinderScalarCoordinateEquiv.toHomeomorph.trans
      (Homeomorph.addRight (0, s))).toOpenPartialHomeomorph).trans
    ((chartAt E2 q).symm.prod (OpenPartialHomeomorph.refl ℝ))

theorem neckVolumeModelChart_apply (q : UnitTwoSphere) (s : ℝ) (x : E) :
    neckVolumeModelChart q s x =
      cylinderSphereParametrization q (cylinderScalarCoordinates s x) := rfl

theorem neckVolumeModelChart_source (q : UnitTwoSphere) (s : ℝ) :
    (neckVolumeModelChart q s).source = univ := by
  ext x
  change (x ∈ (univ : Set E) ∧
    (cylinderScalarCoordinates s x).1 ∈ (chartAt E2 q).target ∧
    (cylinderScalarCoordinates s x).2 ∈ (univ : Set ℝ)) ↔ x ∈ (univ : Set E)
  simp only [sphere_chart_target, mem_univ, and_self]

theorem neckVolumeModelChart_zero (q : UnitTwoSphere) (s : ℝ) :
    neckVolumeModelChart q s 0 = (q, s) := by
  rw [neckVolumeModelChart_apply, cylinderScalarCoordinates_zero]
  change ((chartAt E2 q).symm 0, s) = (q, s)
  rw [← PoincareConjecture.Proofs.M28.NeckAnalysis.sphere_chart_center q,
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

def neckVolumeChart (N : EpsilonNeck g) (q : UnitTwoSphere) (s : ℝ) :
    OpenPartialHomeomorph E M :=
  (neckVolumeModelChart q s).trans (neckCoordinateHomeomorph N)

theorem neckVolumeChart_apply (N : EpsilonNeck g) (q : UnitTwoSphere)
    (s : ℝ) (x : E) :
    neckVolumeChart N q s x = cylinderNeckChart N q s x := rfl

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

theorem neckVolumeChart_smooth (N : EpsilonNeck g) (q : UnitTwoSphere) (s : ℝ) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (neckVolumeChart N q s)
      (neckVolumeChart N q s).source := by
  rw [neckVolumeChart_source]
  exact contMDiffOn_cylinderNeckChart N q s

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

end PoincareConjecture.M28
