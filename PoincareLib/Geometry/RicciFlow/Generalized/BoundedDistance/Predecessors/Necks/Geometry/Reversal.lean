import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Predecessors.Necks.Spheres.RoundCylinderPullbackReflection

/-!
# The literal reversed epsilon-neck

Morgan--Tian Definition 2.18, p. 31, reverses the line coordinate while
retaining the full metric comparison and the same central sphere. This
constructor supplies that actual frozen record for the orientation choices
in A.12-A.18. See the actual-neck-reversal inventory in tasks/M25/derivations.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT

/-- Reflection of the actual open interval subtype in Definition 2.18,
p. 31, valid also when that subtype is empty. -/
noncomputable def neckDomainAxialReflection (epsilon : ℝ) :
    Homeomorph (NeckDomain epsilon) (NeckDomain epsilon) where
  toFun := fun z => (z.1, ⟨-z.2.1, by
    constructor <;> linarith [z.2.2.1, z.2.2.2]⟩)
  invFun := fun z => (z.1, ⟨-z.2.1, by
    constructor <;> linarith [z.2.2.1, z.2.2.2]⟩)
  left_inv := by intro z; ext <;> simp
  right_inv := by intro z; ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- The full reversed neck of Definition 2.18, p. 31. Both displayed total
maps are literal reflections; all scalar, carrier and sphere data are retained. -/
noncomputable def EpsilonNeck.reverse
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) : EpsilonNeck g where
  epsilon := N.epsilon
  epsilon_pos := N.epsilon_pos
  epsilon_lt_half := N.epsilon_lt_half
  scale := N.scale
  scale_pos := N.scale_pos
  center := N.center
  connection := N.connection
  scalar_center_pos := N.scalar_center_pos
  scale_eq_scalar := N.scale_eq_scalar
  carrier := N.carrier
  carrier_open := N.carrier_open
  coordinate := (neckDomainAxialReflection N.epsilon).trans N.coordinate
  coordinate_map := fun z => N.coordinate_map (z.1, -z.2)
  coordinate_map_eq := fun z => N.coordinate_map_eq (neckDomainAxialReflection N.epsilon z)
  coordinate_map_smooth := by
    apply N.coordinate_map_smooth.comp roundCylinderAxialReflection.contMDiff.contMDiffOn
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    change -N.epsilon⁻¹ < -z.2 ∧ -z.2 < N.epsilon⁻¹
    constructor <;> linarith [hz.2.1, hz.2.2]
  coordinate_inverse := fun x => ((N.coordinate_inverse x).1, -(N.coordinate_inverse x).2)
  coordinate_inverse_mem := by
    intro x hx
    have hm := (N.coordinate_inverse_mem x hx).2
    exact ⟨mem_univ _, by linarith [hm.2], by linarith [hm.1]⟩
  coordinate_inverse_left := by
    intro z
    change roundCylinderAxialReflection
      (N.coordinate_inverse (N.coordinate (neckDomainAxialReflection N.epsilon z))) =
        (z.1, (z.2 : ℝ))
    rw [N.coordinate_inverse_left]
    change (z.1, - -(z.2 : ℝ)) = (z.1, (z.2 : ℝ))
    simp
  coordinate_inverse_right := by
    intro x hx
    simpa [neckDomainAxialReflection] using N.coordinate_inverse_right x hx
  coordinate_inverse_smooth :=
    roundCylinderAxialReflection.contMDiff.comp_contMDiffOn N.coordinate_inverse_smooth
  central_sphere := N.central_sphere
  central_sphere_eq := by
    rw [N.central_sphere_eq]
    apply Set.image_congr
    intro z hz
    have hz0 : z.2 = 0 := hz.2
    congr 1
    ext <;> simp [hz0]
  center_on_central_sphere := N.center_on_central_sphere
  central_sphere_subset := N.central_sphere_subset
  metric_comparison := N.metric_comparison.axialReflection N.coordinate_map_smooth

/-- The new neck has the exact reversal relation prescribed in
Definition 2.18, p. 31, in the required source-to-selected direction. -/
theorem EpsilonNeck.sameUpToReversal_reverse
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) :
    N.SameUpToReversal N.reverse := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, -1, Or.inr rfl, ?_⟩
  intro z _
  change N.coordinate_map z = N.coordinate_map (z.1, -(-1 * z.2))
  simp

/-- The actual carrier-restricted intervals exchange ends under reversal;
Definition 2.18, p. 31, and the orientation convention in A.12, p. 504. -/
theorem EpsilonNeck.reverse_region
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) (a b : ℝ) :
    N.reverse.region a b = N.region (-b) (-a) := by
  ext x
  change (x ∈ N.carrier ∧ a < -(N.coordinate_inverse x).2 ∧
      -(N.coordinate_inverse x).2 < b) ↔
    (x ∈ N.carrier ∧ -b < (N.coordinate_inverse x).2 ∧
      (N.coordinate_inverse x).2 < -a)
  constructor <;> rintro ⟨hx, ha, hb⟩ <;> exact ⟨hx, by linarith, by linarith⟩

end PoincareMT
