import PoincareConjecture.Proofs.M47.BlowupControlsCapAffineCoordinates
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNeckSets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



noncomputable def capAffineNeck (N : EpsilonNeck g)
    {epsilon lambda c : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_lt : epsilon < 1 / 2) (hlambda : 0 < lambda)
    (hdomain : ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      lambda * s + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (q : UnitTwoSphere) (hscalar :
      0 < N.connection.scalarCurvature (N.coordinate_map (q, c)))
    (hclose : RoundCylinderClose epsilon 0 (fun z v w =>
      N.connection.scalarCurvature (N.coordinate_map (q, c)) *
        roundCylinderPullback g (N.coordinate_map ∘ neckAxialSpaceMap lambda c) z v w)) :
    EpsilonNeck g := by
  let x := N.coordinate_map (q, c)
  let r := N.connection.scalarCurvature x ^ (-1 / 2 : ℝ)
  let carrier := N.region (c - lambda * epsilon⁻¹) (c + lambda * epsilon⁻¹)
  let coordinate := capAffineNeckCoordinate N hlambda hdomain
  let coordinateMap := N.coordinate_map ∘ neckAxialSpaceMap lambda c
  let inverse := neckAxialInverse lambda c ∘ N.coordinate_inverse
  let sphere := coordinateMap '' (univ ×ˢ ({0} : Set ℝ))
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr hepsilon), inv_pos.mpr hepsilon⟩
  have hcarrier : IsOpen carrier := N.region_isOpen _ _
  have hmap (z : NeckDomain epsilon) :
      (coordinate z : M) = coordinateMap (z.1, (z.2 : ℝ)) := by
    exact capAffineNeckCoordinate_map_eq N hlambda hdomain z
  have hcenter : x ∈ sphere := by
    refine ⟨(q, 0), ⟨mem_univ _, rfl⟩, ?_⟩
    simp only [coordinateMap, Function.comp_apply, neckAxialSpaceMap,
      mul_zero, zero_add]
    rfl
  have hsphere : sphere ⊆ carrier := by
    rintro y ⟨z, hz, rfl⟩
    have hz0 : z.2 = 0 := hz.2
    have hzold : c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      simpa only [mul_zero, zero_add] using hdomain 0 hzero
    change N.coordinate_map (z.1, lambda * z.2 + c) ∈ carrier
    rw [hz0, mul_zero, zero_add]
    refine ⟨N.coordinate_map_mem_of_axial_mem hzold, ?_⟩
    rw [N.coordinate_inverse_coordinate_map_of_axial_mem hzold]
    constructor <;> nlinarith [hlambda, inv_pos.mpr hepsilon]
  have hr : r⁻¹ ^ 2 = N.connection.scalarCurvature x := by
    dsimp [r, x]
    rw [inv_pow, ← Real.rpow_mul_natCast hscalar.le (-1 / 2) 2]
    norm_num [Real.rpow_neg_one]
  let N' : EpsilonNeck g := {
    epsilon := epsilon
    epsilon_pos := hepsilon
    epsilon_lt_half := hepsilon_lt
    scale := r
    scale_pos := Real.rpow_pos_of_pos hscalar _
    center := x
    connection := N.connection
    scalar_center_pos := hscalar
    scale_eq_scalar := rfl
    carrier := carrier
    carrier_open := hcarrier
    coordinate := coordinate
    coordinate_map := coordinateMap
    coordinate_map_eq := fun z => hmap z
    coordinate_map_smooth := capAffineNeckCoordinate_map_smooth N hdomain
    coordinate_inverse := inverse
    coordinate_inverse_mem := fun y hy =>
      capAffineNeckCoordinate_inverse_mem N hlambda hy
    coordinate_inverse_left := fun z =>
      capAffineNeckCoordinate_inverse_left N hlambda hdomain z
    coordinate_inverse_right := fun y hy =>
      (coordinate.apply_symm_apply ⟨y, hy⟩)
    coordinate_inverse_smooth := capAffineNeckCoordinate_inverse_smooth N epsilon lambda c
    central_sphere := sphere
    central_sphere_eq := rfl
    center_on_central_sphere := hcenter
    central_sphere_subset := hsphere
    metric_comparison := by
      refine ⟨?_⟩
      simpa only [coordinateMap, hr] using hclose }
  exact N'

theorem capAffineNeck_fields (N : EpsilonNeck g)
    {epsilon lambda c : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_lt : epsilon < 1 / 2) (hlambda : 0 < lambda)
    (hdomain : ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      lambda * s + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (q : UnitTwoSphere) (hscalar :
      0 < N.connection.scalarCurvature (N.coordinate_map (q, c)))
    (hclose : RoundCylinderClose epsilon 0 (fun z v w =>
      N.connection.scalarCurvature (N.coordinate_map (q, c)) *
        roundCylinderPullback g (N.coordinate_map ∘ neckAxialSpaceMap lambda c) z v w)) :
    (capAffineNeck N hepsilon hepsilon_lt hlambda hdomain q hscalar hclose).center =
      N.coordinate_map (q, c) := by
  rfl

end PoincareConjecture.M47
