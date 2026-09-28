import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Cylinder
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Centered
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder

noncomputable section

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace PoincareConjecture

namespace OpenCylinderModel

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

def toDiffeomorph (U : Opens M) (T : OpenCylinderModel (U : Set M)) :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) domain U ∞ where
  toFun z := ⟨T.coordinate z, by
    have h := (T.homeomorph (z.1.1, ⟨z.1.2, z.property.2⟩)).property
    rwa [T.coordinate_eq] at h⟩
  invFun x := ⟨T.inverse x, T.inverse_mem x x.property⟩
  left_inv z := Subtype.ext (T.left_inverse z.property)
  right_inv x := Subtype.ext (T.right_inverse x.property)
  contMDiff_toFun := by
    rw [← ContMDiff.subtypeVal_comp_iff U]
    exact T.coordinate_smooth.comp_contMDiff contMDiff_subtype_val fun z => z.property
  contMDiff_invFun := by
    rw [← ContMDiff.subtypeVal_comp_iff domain]
    exact T.inverse_smooth.comp_contMDiff contMDiff_subtype_val fun x => x.property

@[simp] theorem toDiffeomorph_apply (U : Opens M) (T : OpenCylinderModel (U : Set M))
    (z : domain) : (T.toDiffeomorph U z : M) = T.coordinate z := rfl

@[simp] theorem toDiffeomorph_symm_apply (U : Opens M) (T : OpenCylinderModel (U : Set M))
    (x : U) : (T.toDiffeomorph U).symm x = ⟨T.inverse x, T.inverse_mem x x.property⟩ := rfl

end OpenCylinderModel

namespace EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem exists_unit_to_real_cylinder (N : EpsilonNeck g) :
    ∃ E : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      OpenCylinderModel.domain RoundCylinderSpace ∞,
      ∀ q : UnitTwoSphere, E ⟨(q, 1 / 2), mem_univ _, by norm_num⟩ = (q, 0) := by
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  obtain ⟨K, _, hKzero, _, _⟩ :=
    N.exists_centered_neck_coordinates (fun _ => 0) contMDiff_const (fun _ => hzero)
  let F := N.openCylinderModel.toDiffeomorph N.carrierOpen
  refine ⟨F.trans K.symm, ?_⟩
  intro q
  let z : OpenCylinderModel.domain := ⟨(q, 1 / 2), mem_univ _, by norm_num⟩
  have hF : (F z : M) = N.coordinate_map (q, 0) := by
    change N.coordinate_map (q, (2 * (1 / 2) - 1) * N.epsilon⁻¹) = _
    norm_num
  have heq : F z = K (q, 0) := Subtype.ext (hF.trans (hKzero q).symm)
  change K.symm (F z) = (q, 0)
  rw [heq, K.symm_apply_apply]

end EpsilonNeck

end PoincareConjecture
