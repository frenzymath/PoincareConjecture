import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Gluing.Construction.RecentNeck

/-!
# The scalar-one neck of an actual cylinder patch

The original patch and its terminal comparison provide every intrinsic
neck field. MT Definition 2.18 and Lemma 17.7;
limit-cap-long-age-canonical.md, L1.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M47

/-- A genuine patch with scalar-one center and its terminal comparison
gives a scale-one neck retaining its metric, carrier and coordinates. -/
theorem exists_scalar_one_patch_neck
    {C : GeneralizedSliceCarrier.{u}} {g : RiemannianMetric 3 C.carrier}
    (D : LeviCivitaData g) {eta : ℝ} {x : C.carrier}
    (patch : M45CylinderPatch C eta⁻¹ x) (heta : 0 < eta) (hsmall : eta < 1 / 2)
    (hscalar : D.scalarCurvature x = 1)
    (hclose : RoundCylinderClose eta 0 (roundCylinderPullback g patch.coordinate)) :
    ∃ N : EpsilonNeck g,
      N.epsilon = eta ∧ N.scale = 1 ∧ N.center = x ∧ N.connection = D ∧
        N.carrier = patch.carrier ∧ N.coordinate_map = patch.coordinate := by
  let N : EpsilonNeck g := {
    epsilon := eta
    epsilon_pos := heta
    epsilon_lt_half := hsmall
    scale := 1
    scale_pos := zero_lt_one
    center := x
    connection := D
    scalar_center_pos := by rw [hscalar]; exact zero_lt_one
    scale_eq_scalar := by rw [hscalar]; simp
    carrier := patch.carrier
    carrier_open := patch.carrier_open
    coordinate := patch.neckHomeomorph
    coordinate_map := patch.coordinate
    coordinate_map_eq := fun _ => rfl
    coordinate_map_smooth := patch.coordinate_smooth
    coordinate_inverse := patch.inverse
    coordinate_inverse_mem := fun y hy => ⟨mem_univ _, patch.inverse_domain y hy⟩
    coordinate_inverse_left := fun z =>
      patch.coordinate_left_inverse ⟨mem_univ z.1, z.2.2⟩
    coordinate_inverse_right := fun y hy => Subtype.ext (patch.coordinate_right_inverse hy)
    coordinate_inverse_smooth := patch.inverse_smooth
    central_sphere := patch.coordinate '' (univ ×ˢ ({0} : Set ℝ))
    central_sphere_eq := rfl
    center_on_central_sphere := by
      obtain ⟨z, hz⟩ := patch.center_sphere
      exact ⟨(z, 0), ⟨mem_univ _, rfl⟩, hz⟩
    central_sphere_subset := by
      rintro y ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩
      have hs0 : s = 0 := hs
      rw [hs0, ← patch.coordinate_image]
      exact ⟨(z, 0), ⟨mem_univ _, by
        constructor <;> linarith [patch.length_pos]⟩, rfl⟩
    metric_comparison := ⟨by simpa only [inv_one, one_pow, one_mul] using hclose⟩ }
  exact ⟨N, rfl, rfl, rfl, rfl, rfl, rfl⟩

end PoincareMT.M47
