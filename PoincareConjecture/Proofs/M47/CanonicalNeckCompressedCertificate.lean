import PoincareConjecture.Proofs.M47.CanonicalNeckCompressedCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g h : RiemannianMetric 3 M}

theorem compressedNeck_map_mem (N : EpsilonNeck g)
    {lambda c : ℝ} (hlambda : lambda ∈ Ioo (0 : ℝ) 1)
    (hc : |c| < (1 - lambda) * N.epsilon⁻¹) {z : RoundCylinderSpace}
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    (N.coordinate_map ∘ neckAxialSpaceMap lambda c) z ∈
      compressedNeckCarrier N lambda c := by
  let z' : NeckDomain N.epsilon := (z.1, ⟨z.2, hz⟩)
  have heq := compressedNeckCoordinate_map_eq N hlambda hc z'
  change (compressedNeckCoordinate N hlambda hc z' : M) =
    (N.coordinate_map ∘ neckAxialSpaceMap lambda c) z at heq
  rw [← heq]
  exact (compressedNeckCoordinate N hlambda hc z').property

theorem compressedNeck_center_on_central_sphere (N : EpsilonNeck g)
    (lambda c : ℝ) (x : M) (hx : x ∈ N.carrier)
    (hheight : (N.coordinate_inverse x).2 = c) :
    x ∈ (N.coordinate_map ∘ neckAxialSpaceMap lambda c) ''
      (univ ×ˢ ({0} : Set ℝ)) := by
  refine ⟨((N.coordinate_inverse x).1, 0), ⟨mem_univ _, mem_singleton 0⟩, ?_⟩
  have h := congrArg (fun y : N.carrier => (y : M))
    (N.coordinate_inverse_right x hx)
  rw [N.coordinate_map_eq] at h
  simpa only [Function.comp_apply, neckAxialSpaceMap, mul_zero, zero_add,
    ← hheight, Prod.mk.eta] using h

theorem exists_compressed_neck_of_normalized_comparison (N : EpsilonNeck g)
    {lambda c : ℝ} (hlambda : lambda ∈ Ioo (0 : ℝ) 1)
    (hc : |c| < (1 - lambda) * N.epsilon⁻¹)
    (x : M) (hx : x ∈ N.carrier) (hheight : (N.coordinate_inverse x).2 = c)
    (D : LeviCivitaData h) (hR : 0 < D.scalarCurvature x)
    (hclose : RoundCylinderClose N.epsilon 0 (fun z v w =>
      D.scalarCurvature x * roundCylinderPullback h
        (N.coordinate_map ∘ neckAxialSpaceMap lambda c) z v w)) :
    ∃ N' : EpsilonNeck h, N'.epsilon = N.epsilon ∧ N'.center = x ∧
      N'.carrier = compressedNeckCarrier N lambda c ∧
      N'.coordinate_map = N.coordinate_map ∘ neckAxialSpaceMap lambda c ∧
      N'.coordinate_inverse = neckAxialInverse lambda c ∘ N.coordinate_inverse ∧
      N'.central_sphere = (N.coordinate_map ∘ neckAxialSpaceMap lambda c) ''
        (univ ×ˢ ({0} : Set ℝ)) ∧
      N'.connection = D ∧ HEq N'.coordinate (compressedNeckCoordinate N hlambda hc) := by
  have hscale : (D.scalarCurvature x ^ (-1 / 2 : ℝ))⁻¹ ^ 2 =
      D.scalarCurvature x := by
    rw [inv_pow, ← Real.rpow_mul_natCast hR.le (-1 / 2) 2]
    norm_num [Real.rpow_neg_one]
  let N' : EpsilonNeck h := {
    epsilon := N.epsilon
    epsilon_pos := N.epsilon_pos
    epsilon_lt_half := N.epsilon_lt_half
    scale := D.scalarCurvature x ^ (-1 / 2 : ℝ)
    scale_pos := Real.rpow_pos_of_pos hR _
    center := x
    connection := D
    scalar_center_pos := hR
    scale_eq_scalar := rfl
    carrier := compressedNeckCarrier N lambda c
    carrier_open := compressedNeckCarrier_isOpen N lambda c
    coordinate := compressedNeckCoordinate N hlambda hc
    coordinate_map := N.coordinate_map ∘ neckAxialSpaceMap lambda c
    coordinate_map_eq := compressedNeckCoordinate_map_eq N hlambda hc
    coordinate_map_smooth := compressedNeckCoordinate_map_smooth N hlambda hc
    coordinate_inverse := neckAxialInverse lambda c ∘ N.coordinate_inverse
    coordinate_inverse_mem := fun _ hx => hx.2
    coordinate_inverse_left := compressedNeckCoordinate_inverse_left N hlambda hc
    coordinate_inverse_right := fun y hy =>
      (compressedNeckCoordinate N hlambda hc).apply_symm_apply ⟨y, hy⟩
    coordinate_inverse_smooth := compressedNeckCoordinate_inverse_smooth N lambda c
    central_sphere := (N.coordinate_map ∘ neckAxialSpaceMap lambda c) ''
      (univ ×ˢ ({0} : Set ℝ))
    central_sphere_eq := rfl
    center_on_central_sphere := compressedNeck_center_on_central_sphere N lambda c x hx hheight
    central_sphere_subset := by
      rintro _ ⟨z, hz, rfl⟩
      apply compressedNeck_map_mem N hlambda hc
      have hz0 : z.2 = 0 := hz.2
      rw [hz0]
      exact ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
    metric_comparison := ⟨by simpa only [hscale] using hclose⟩ }
  exact ⟨N', rfl, rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl⟩

end PoincareConjecture.Proofs.M47
