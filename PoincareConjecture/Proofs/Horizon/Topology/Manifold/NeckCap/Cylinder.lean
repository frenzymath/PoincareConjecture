import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Charts
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Models








noncomputable section

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

private theorem normalizedAxial_mem {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (2 * t - 1) * N.epsilon⁻¹ ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
  have hε := inv_pos.mpr N.epsilon_pos
  constructor
  · nlinarith [mul_pos ht.1 hε]
  · nlinarith [mul_pos (sub_pos.mpr ht.2) hε]

private theorem inverseNormalizedAxial_mem {t : ℝ}
    (ht : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    (t * N.epsilon + 1) / 2 ∈ Ioo (0 : ℝ) 1 := by
  have hlo := (mul_lt_mul_of_pos_right ht.1 N.epsilon_pos)
  have hhi := (mul_lt_mul_of_pos_right ht.2 N.epsilon_pos)
  simp only [neg_mul, inv_mul_cancel₀ N.epsilon_pos.ne'] at hlo hhi
  constructor <;> linarith


def unitIntervalHomeomorph : Ioo (0 : ℝ) 1 ≃ₜ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ where
  toFun t := ⟨(2 * t.1 - 1) * N.epsilon⁻¹, N.normalizedAxial_mem t.2⟩
  invFun t := ⟨(t.1 * N.epsilon + 1) / 2, N.inverseNormalizedAxial_mem t.2⟩
  left_inv t := by
    apply Subtype.ext
    dsimp
    field_simp [N.epsilon_pos.ne']
    ring
  right_inv t := by
    apply Subtype.ext
    dsimp
    field_simp [N.epsilon_pos.ne']
    ring
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop


def openCylinderModel : OpenCylinderModel N.carrier where
  homeomorph := ((Homeomorph.refl UnitTwoSphere).prodCongr N.unitIntervalHomeomorph).trans
    N.coordinate
  coordinate z := N.coordinate_map (z.1, (2 * z.2 - 1) * N.epsilon⁻¹)
  coordinate_eq z := N.coordinate_map_eq (z.1, N.unitIntervalHomeomorph z.2)
  coordinate_smooth := by
    apply N.coordinate_map_smooth.comp
      (contMDiff_fst.prodMk
        ((((contDiff_const.mul contDiff_id).sub contDiff_const).mul
          contDiff_const).contMDiff.comp contMDiff_snd)).contMDiffOn
    intro z hz
    exact ⟨mem_univ _, N.normalizedAxial_mem hz.2⟩
  inverse x := ((N.coordinate_inverse x).1, ((N.coordinate_inverse x).2 * N.epsilon + 1) / 2)
  inverse_mem x hx := ⟨mem_univ _,
    N.inverseNormalizedAxial_mem (N.coordinate_inverse_mem x hx).2⟩
  left_inverse := by
    intro z hz
    dsimp
    rw [N.coordinate_inverse_coordinate_map
      (show (z.1, (2 * z.2 - 1) * N.epsilon⁻¹) ∈ N.cylinderDomain from
        ⟨mem_univ _, N.normalizedAxial_mem hz.2⟩)]
    refine Prod.ext rfl ?_
    dsimp
    field_simp [N.epsilon_pos.ne']
    ring
  right_inverse := by
    intro x hx
    dsimp
    have heq : (2 * (((N.coordinate_inverse x).2 * N.epsilon + 1) / 2) - 1) *
        N.epsilon⁻¹ = (N.coordinate_inverse x).2 := by
      field_simp [N.epsilon_pos.ne']
      ring
    rw [heq]
    exact N.coordinate_map_coordinate_inverse hx
  inverse_smooth := by
    exact (contMDiff_fst.comp_contMDiffOn N.coordinate_inverse_smooth).prodMk
      ((((contDiff_id.mul contDiff_const).add contDiff_const).div_const 2).contMDiff.comp
        contMDiff_snd |>.comp_contMDiffOn N.coordinate_inverse_smooth)

@[simp] theorem openCylinderModel_middleSphere :
    N.openCylinderModel.middleSphere = N.central_sphere := by
  rw [N.central_sphere_eq]
  apply Set.ext
  intro x
  constructor
  · rintro ⟨⟨p, t⟩, ⟨_, ht⟩, hx⟩
    have ht' : t = 1 / 2 := ht
    subst t
    refine ⟨(p, 0), ⟨mem_univ _, mem_singleton 0⟩, ?_⟩
    simpa [openCylinderModel] using hx
  · rintro ⟨⟨p, t⟩, ⟨_, ht⟩, hx⟩
    have ht' : t = 0 := ht
    subst t
    refine ⟨(p, 1 / 2), ⟨mem_univ _, mem_singleton _⟩, ?_⟩
    simpa [openCylinderModel] using hx

end PoincareConjecture.EpsilonNeck
