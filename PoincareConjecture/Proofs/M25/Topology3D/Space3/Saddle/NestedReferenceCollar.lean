import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedReferenceModel
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarRadialCoordinates
import Mathlib.Geometry.Manifold.MFDeriv.Atlas









set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D




theorem exists_nestedReference_collar (d : ℝ) :
    let psi : UnitTwoSphere × ℝ → E3 :=
      fun p => nestedReferenceDiffeomorph d ((1 + p.2) • (p.1 : E3))
    IsCollarEmbedding psi ∧
    Set.range (fun q : UnitTwoSphere => psi (q, 0)) =
      (nestedReferenceBallChart d).boundary ∧
    (∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Set.Ioo (-1) 1 →
      (psi (q, s) ∈ (nestedReferenceBallChart d).inside ↔ s < 0) ∧
      (psi (q, s) ∈ (nestedReferenceBallChart d).closedRegion ↔ s ≤ 0) ∧
      (psi (q, s) ∈ (nestedReferenceBallChart d).boundary ↔ s = 0)) ∧
    ∃ C : OpenPartialHomeomorph (UnitTwoSphere × ℝ) E3,
      C.source = Set.univ ×ˢ Set.Ioo (-1) 1 ∧
      C.target = (nestedReferenceDiffeomorph d) ''
        {y : E3 | 0 < ‖y‖ ∧ ‖y‖ < 2} ∧
      (C : UnitTwoSphere × ℝ → E3) = psi ∧
      (∀ y ∈ C.target, C.symm y =
        (sphereDirection ((nestedReferenceDiffeomorph d).symm y),
          ‖(nestedReferenceDiffeomorph d).symm y‖ - 1)) ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ C C.source ∧
      ContMDiffOn 𝓘(ℝ, E3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ C.symm C.target := by
  let F := nestedReferenceDiffeomorph d
  let psi : UnitTwoSphere × ℝ → E3 := fun p => F ((1 + p.2) • (p.1 : E3))
  change IsCollarEmbedding psi ∧ _
  obtain ⟨e, hes, het, hef, hei, he, heinv⟩ :=
    exists_collar_radial_coordinates
      (Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞)
      (side := (1 : ℝ)) (by norm_num)
  let C := e.symm.trans F.toHomeomorph.toOpenPartialHomeomorph
  have hCs : C.source = univ ×ˢ Ioo (-1 : ℝ) 1 := by
    change e.target ∩ e.symm ⁻¹' (univ : Set E3) = _
    simpa only [preimage_univ, inter_univ] using het
  have hCt : C.target = F '' {y : E3 | 0 < ‖y‖ ∧ ‖y‖ < 2} := by
    change (e.symm.trans F.toHomeomorph.toOpenPartialHomeomorph).target = _
    rw [OpenPartialHomeomorph.trans_target'']
    change F '' ((univ : Set E3) ∩ e.source) = _
    rw [univ_inter, hes]
  have hCf : (C : UnitTwoSphere × ℝ → E3) = psi := by
    funext p
    change F (e.symm p) = F ((1 + p.2) • (p.1 : E3))
    rw [hei]
    simp only [one_mul, Diffeomorph.coe_refl, id_eq]
  have hC : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ C C.source :=
    F.contMDiff.comp_contMDiffOn (heinv.mono inter_subset_left)
  have hCi : ContMDiffOn 𝓘(ℝ, E3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      C.symm C.target :=
    he.comp F.symm.contMDiff.contMDiffOn (fun _ hy => hy.2)
  have hCdiff : C.MDifferentiable ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) :=
    ⟨hC.mdifferentiableOn (by simp), hCi.mdifferentiableOn (by simp)⟩
  have hpsi : IsCollarEmbedding psi := by
    rw [← hCf]
    refine ⟨by simpa only [hCs] using hC, ?_, ?_⟩
    · intro p hp q hq hpq
      exact C.injOn (hCs.symm ▸ hp) (hCs.symm ▸ hq) hpq
    · intro p hp
      exact hCdiff.mfderiv_injective (hCs.symm ▸ hp)
  have hmem (S : Set E3) (x : E3) : F x ∈ F '' S ↔ x ∈ S := by
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact F.injective hxy ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hregions (x : E3) :
      (F x ∈ (nestedReferenceBallChart d).inside ↔ ‖x‖ < 1) ∧
      (F x ∈ (nestedReferenceBallChart d).closedRegion ↔ ‖x‖ ≤ 1) ∧
      (F x ∈ (nestedReferenceBallChart d).boundary ↔ ‖x‖ = 1) := by
    change (F x ∈ F '' ball 0 1 ↔ ‖x‖ < 1) ∧
      (F x ∈ F '' closedBall 0 1 ↔ ‖x‖ ≤ 1) ∧
      (F x ∈ F '' sphere 0 1 ↔ ‖x‖ = 1)
    simp only [hmem, mem_ball_zero_iff, mem_closedBall_zero_iff,
      mem_sphere_zero_iff_norm, and_self]
  refine ⟨hpsi, ?_, ?_, C, hCs, hCt, hCf, ?_, hC, hCi⟩
  · change range (fun q : UnitTwoSphere => F ((1 + (0 : ℝ)) • (q : E3))) =
      F '' sphere 0 1
    simp only [add_zero, one_smul]
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨(q : E3), q.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(⟨x, hx⟩ : UnitTwoSphere), rfl⟩
  · intro q s hs
    have hpositive : 0 < 1 + s := by linarith [hs.1]
    have hnorm : ‖(1 + s) • (q : E3)‖ = 1 + s := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpositive,
        norm_eq_of_mem_sphere, mul_one]
    obtain ⟨hi, hc, hb⟩ := hregions ((1 + s) • (q : E3))
    change (F ((1 + s) • (q : E3)) ∈ _ ↔ _) ∧ _
    rw [hi, hc, hb, hnorm]
    constructor
    · constructor <;> intro h <;> linarith
    · constructor <;> constructor <;> intro h <;> linarith
  · intro y _hy
    change e (F.symm y) = (sphereDirection (F.symm y), ‖F.symm y‖ - 1)
    rw [hef]
    simp only [one_mul, Diffeomorph.symm_refl, Diffeomorph.coe_refl, id_eq]

end PoincareConjecture.M25.Topology3D
