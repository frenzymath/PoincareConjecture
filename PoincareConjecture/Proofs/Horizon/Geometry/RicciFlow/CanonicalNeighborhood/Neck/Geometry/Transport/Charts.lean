import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Model








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

def cylinderDomain : Set RoundCylinderSpace :=
  univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹

theorem cylinderDomain_open : IsOpen N.cylinderDomain := isOpen_univ.prod isOpen_Ioo

theorem coordinate_map_mem {z : RoundCylinderSpace} (hz : z ∈ N.cylinderDomain) :
    N.coordinate_map z ∈ N.carrier := by
  let w : NeckDomain N.epsilon := (z.1, ⟨z.2, hz.2⟩)
  have hw := (N.coordinate w).property
  rw [N.coordinate_map_eq] at hw
  exact hw

theorem coordinate_inverse_coordinate_map {z : RoundCylinderSpace}
    (hz : z ∈ N.cylinderDomain) : N.coordinate_inverse (N.coordinate_map z) = z := by
  let w : NeckDomain N.epsilon := (z.1, ⟨z.2, hz.2⟩)
  have hw := N.coordinate_inverse_left w
  rw [N.coordinate_map_eq] at hw
  exact hw

theorem coordinate_map_coordinate_inverse {x : M} (hx : x ∈ N.carrier) :
    N.coordinate_map (N.coordinate_inverse x) = x := by
  have hw := congrArg Subtype.val (N.coordinate_inverse_right x hx)
  rw [N.coordinate_map_eq] at hw
  exact hw

def coordinatePartialHomeomorph : OpenPartialHomeomorph RoundCylinderSpace M where
  toFun := N.coordinate_map
  invFun := N.coordinate_inverse
  source := N.cylinderDomain
  target := N.carrier
  map_source' := fun _ hz ↦ N.coordinate_map_mem hz
  map_target' := N.coordinate_inverse_mem
  left_inv' := fun _ hz ↦ N.coordinate_inverse_coordinate_map hz
  right_inv' := fun _ hx ↦ N.coordinate_map_coordinate_inverse hx
  open_source := N.cylinderDomain_open
  open_target := N.carrier_open
  continuousOn_toFun := N.coordinate_map_smooth.continuousOn
  continuousOn_invFun := N.coordinate_inverse_smooth.continuousOn

@[simp] theorem coordinatePartialHomeomorph_apply (z : RoundCylinderSpace) :
    N.coordinatePartialHomeomorph z = N.coordinate_map z := rfl

@[simp] theorem coordinatePartialHomeomorph_symm_apply (x : M) :
    N.coordinatePartialHomeomorph.symm x = N.coordinate_inverse x := rfl

theorem coordinate_map_flat_smooth :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ N.coordinate_map N.cylinderDomain := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  let e := roundCylinderModelDiffeomorph
  have he : (e.symm : RoundCylinderSpace → RoundCylinderSpace) = id := rfl
  have h := N.coordinate_map_smooth.comp e.symm.contMDiff.contMDiffOn
    (show MapsTo e.symm N.cylinderDomain N.cylinderDomain from by rw [he]; exact mapsTo_id _)
  simpa only [he, Function.comp_id] using h

theorem coordinate_inverse_flat_smooth :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ N.coordinate_inverse N.carrier := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  let e := roundCylinderModelDiffeomorph
  have he : (e : RoundCylinderSpace → RoundCylinderSpace) = id := rfl
  have h := e.contMDiff.comp_contMDiffOn N.coordinate_inverse_smooth
  simpa only [he, Function.id_comp] using h

end PoincareConjecture.EpsilonNeck
