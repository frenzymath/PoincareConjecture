import PoincareConjecture.Proofs.M45.Ch12_Standard.NeckReflectionGeometry
import PoincareConjecture.Proofs.M36.NeckCoordinates









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M45


def neckDomainReflection (epsilon : ℝ) : NeckDomain epsilon ≃ₜ NeckDomain epsilon where
  toFun z := (z.1, ⟨-z.2.1, by constructor <;> linarith [z.2.2.1, z.2.2.2]⟩)
  invFun z := (z.1, ⟨-z.2.1, by constructor <;> linarith [z.2.2.1, z.2.2.2]⟩)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).neg.subtype_mk _)
  continuous_invFun := continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).neg.subtype_mk _)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



noncomputable def reverseNeck (N : EpsilonNeck g) : EpsilonNeck g where
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
  coordinate := (neckDomainReflection N.epsilon).trans N.coordinate
  coordinate_map := N.coordinate_map ∘ cylinderAxialReflection
  coordinate_map_eq := fun z => N.coordinate_map_eq (neckDomainReflection N.epsilon z)
  coordinate_map_smooth := N.coordinate_map_smooth.comp
    cylinderAxialReflection_smooth.contMDiffOn (by
      intro z hz
      exact ⟨mem_univ _, by
        change -N.epsilon⁻¹ < -z.2 ∧ -z.2 < N.epsilon⁻¹
        constructor <;> linarith [hz.2.1, hz.2.2]⟩)
  coordinate_inverse := cylinderAxialReflection ∘ N.coordinate_inverse
  coordinate_inverse_mem := by
    intro x hx
    have h := N.coordinate_inverse_mem x hx
    exact ⟨mem_univ _, by
      change -N.epsilon⁻¹ < -(N.coordinate_inverse x).2 ∧
        -(N.coordinate_inverse x).2 < N.epsilon⁻¹
      constructor <;> linarith [h.2.1, h.2.2]⟩
  coordinate_inverse_left := by
    intro z
    change cylinderAxialReflection
      (N.coordinate_inverse (N.coordinate (neckDomainReflection N.epsilon z))) = _
    rw [N.coordinate_inverse_left]
    simp [neckDomainReflection, cylinderAxialReflection]
  coordinate_inverse_right := by
    intro x hx
    apply Subtype.ext
    change (N.coordinate _ : M) = x
    rw [N.coordinate_map_eq]
    change N.coordinate_map ((N.coordinate_inverse x).1, - -(N.coordinate_inverse x).2) = x
    simpa only [neg_neg] using M36.neck_coordinate_inverse N hx
  coordinate_inverse_smooth :=
    cylinderAxialReflection_smooth.comp_contMDiffOn N.coordinate_inverse_smooth
  central_sphere := N.central_sphere
  central_sphere_eq := by
    rw [N.central_sphere_eq]
    ext x
    constructor <;> rintro ⟨z, hz, rfl⟩
    · refine ⟨z, hz, ?_⟩
      have hz0 : z.2 = 0 := hz.2
      apply congrArg N.coordinate_map
      apply Prod.ext
      · rfl
      · change -z.2 = z.2
        simp only [hz0, neg_zero]
    · refine ⟨cylinderAxialReflection z, ⟨mem_univ _, ?_⟩, rfl⟩
      have hz0 : z.2 = 0 := hz.2
      simp [cylinderAxialReflection, hz0]
  center_on_central_sphere := N.center_on_central_sphere
  central_sphere_subset := N.central_sphere_subset
  metric_comparison := neckMetricComparison_reflection g N.metric_comparison



theorem reverseNeck_region (N : EpsilonNeck g) (a b : ℝ) :
    (reverseNeck N).region a b = N.region (-b) (-a) := by
  ext x
  change (x ∈ N.carrier ∧ a < -(N.coordinate_inverse x).2 ∧
    -(N.coordinate_inverse x).2 < b) ↔
      x ∈ N.carrier ∧ -b < (N.coordinate_inverse x).2 ∧
        (N.coordinate_inverse x).2 < -a
  constructor <;> rintro ⟨hx, h₁, h₂⟩ <;> exact ⟨hx, by linarith, by linarith⟩

end PoincareConjecture.M45
