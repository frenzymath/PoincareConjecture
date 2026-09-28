import PoincareConjecture.Proofs.M25.AppA_1_Necks.RoundCylinderPullbackReflection

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

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

theorem EpsilonNeck.sameUpToReversal_reverse
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) :
    N.SameUpToReversal N.reverse := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, -1, Or.inr rfl, ?_⟩
  intro z _
  change N.coordinate_map z = N.coordinate_map (z.1, -(-1 * z.2))
  simp

theorem EpsilonNeck.reverse_region
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) (a b : ℝ) :
    N.reverse.region a b = N.region (-b) (-a) := by
  ext x
  change (x ∈ N.carrier ∧ a < -(N.coordinate_inverse x).2 ∧
      -(N.coordinate_inverse x).2 < b) ↔
    (x ∈ N.carrier ∧ -b < (N.coordinate_inverse x).2 ∧
      (N.coordinate_inverse x).2 < -a)
  constructor <;> rintro ⟨hx, ha, hb⟩ <;> exact ⟨hx, by linarith, by linarith⟩

end PoincareConjecture
