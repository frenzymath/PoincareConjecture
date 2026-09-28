import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarRadialCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SouthernSphereChart









set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D


noncomputable def nativeCapAmbientDiffeomorph
    (ψ : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (tag : SurgeryCapTag ψ u) :
    Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E2 × ℝ) E3 (E2 × ℝ) ∞ :=
  surgeryCapAmbientDiffeomorph tag.profile.horizontal tag.profile.vertical
    tag.profile.horizontal_smooth tag.profile.vertical_smooth
    (fun z => (tag.profile.horizontal_pos z).ne')
    (fun x => (tag.profile.vertical_pos x).ne')
    tag.cutHeight tag.sign tag.removal tag.scale
    (by
      intro hz
      have habs := tag.sign_abs
      rw [hz, abs_zero] at habs
      exact zero_ne_one habs)
    tag.scale_pos.ne'


theorem nativeCapAmbientDiffeomorph_spec
    (ψ : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (tag : SurgeryCapTag ψ u) :
    let D := nativeCapAmbientDiffeomorph ψ u tag
    (∀ y : E3,
      let p := heightCoordinates y
      let X := tag.profile.horizontal p.2 • p.1
      D y = (X, tag.cutHeight + tag.sign *
        (tag.removal + tag.scale * (tag.profile.vertical X * p.2)))) ∧
    (∀ p : E2 × ℝ,
      let z := (tag.profile.vertical p.1)⁻¹ *
        (tag.scale⁻¹ * (tag.sign⁻¹ * (p.2 - tag.cutHeight) - tag.removal))
      D.symm p = heightCoordinates.symm
        ((tag.profile.horizontal z)⁻¹ • p.1, z)) ∧
    (∀ q : UnitTwoSphere, D (q : E3) ∈ tag.tube.source ∧
      tag.tube (D (q : E3)) = tag.profile.capMap tag.tube
        tag.cutHeight tag.sign tag.removal tag.scale q) ∧
    ∀ r : ℝ, D (r • (southSpherePoint (0 : E2) : E3)) =
      (0, tag.cutHeight + tag.sign * (tag.removal - tag.scale * r)) := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro q
    refine ⟨?_, rfl⟩
    exact surgeryCapCoordinates_mem_tube_source
      tag.profile.horizontal tag.profile.vertical
      tag.profile.horizontal_smooth tag.profile.vertical_smooth
      (fun z => (tag.profile.horizontal_pos z).ne')
      (fun x => (tag.profile.vertical_pos x).ne')
      tag.profile.horizontal_pos tag.profile.horizontal_bound tag.tube tag.tube_source
      tag.cutHeight tag.sign tag.removal tag.scale q
  · intro r
    have hs : heightCoordinates (southSpherePoint (0 : E2) : E3) = (0, -1) := by
      simpa using southSpherePoint_coordinates (0 : E2) (by norm_num)
    have hcoords : heightCoordinates (r • (southSpherePoint (0 : E2) : E3)) =
        (0, -r) := by
      rw [map_smul, hs]
      simp
    have hbzero : tag.profile.vertical (0 : E2) = 1 := by
      simpa using tag.profile.vertical_near (0 : E2) (by norm_num)
    change (tag.profile.horizontal
        (heightCoordinates (r • (southSpherePoint (0 : E2) : E3))).2 •
          (heightCoordinates (r • (southSpherePoint (0 : E2) : E3))).1,
      tag.cutHeight + tag.sign * (tag.removal + tag.scale *
        (tag.profile.vertical (tag.profile.horizontal
          (heightCoordinates (r • (southSpherePoint (0 : E2) : E3))).2 •
            (heightCoordinates (r • (southSpherePoint (0 : E2) : E3))).1) *
          (heightCoordinates (r • (southSpherePoint (0 : E2) : E3))).2))) = _
    rw [hcoords]
    simp only [smul_zero, hbzero, one_mul, mul_neg, sub_eq_add_neg]


noncomputable def nativeCapRadialChart
    (ψ : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (tag : SurgeryCapTag ψ u)
    (Q : OpenPartialHomeomorph E2 UnitTwoSphere)
    (e : ℝ) (he : e * e = 1) :
    OpenPartialHomeomorph (E2 × ℝ) E3 :=
  let r := Classical.choose
    (exists_collar_radial_coordinates (Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞) he)
  let R := (Q.prod (OpenPartialHomeomorph.refl ℝ)).trans r.symm
  (R.trans (nativeCapAmbientDiffeomorph ψ u tag).toHomeomorph.toOpenPartialHomeomorph).trans
    tag.tube


theorem nativeCapRadialChart_spec
    (ψ : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (tag : SurgeryCapTag ψ u)
    (Q : OpenPartialHomeomorph E2 UnitTwoSphere)
    (hQ : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ Q Q.source)
    (hQi : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ Q.symm Q.target)
    (e : ℝ) (he : e * e = 1) :
    let D := nativeCapAmbientDiffeomorph ψ u tag
    let C := nativeCapRadialChart ψ u tag Q e he
    C.source = {p : E2 × ℝ | p.1 ∈ Q.source ∧ p.2 ∈ Ioo (-1) 1 ∧
      D ((1 + e * p.2) • (Q p.1 : E3)) ∈ tag.tube.source} ∧
    C.target = {Y : E3 | Y ∈ tag.tube.target ∧
      0 < ‖D.symm (tag.tube.symm Y)‖ ∧
      ‖D.symm (tag.tube.symm Y)‖ < 2 ∧
      sphereDirection (D.symm (tag.tube.symm Y)) ∈ Q.target} ∧
    (∀ p : E2 × ℝ,
      C p = tag.tube (D ((1 + e * p.2) • (Q p.1 : E3)))) ∧
    (∀ Y : E3, C.symm Y =
      (Q.symm (sphereDirection (D.symm (tag.tube.symm Y))),
        e * (‖D.symm (tag.tube.symm Y)‖ - 1))) ∧
    ContDiffOn ℝ ∞ C C.source ∧
    ContDiffOn ℝ ∞ C.symm C.target ∧
    ∀ X ∈ Q.source, (X, (0 : ℝ)) ∈ C.source ∧
      C (X, 0) = tag.profile.capMap tag.tube tag.cutHeight tag.sign
        tag.removal tag.scale (Q X) := by
  let hex := exists_collar_radial_coordinates
    (Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞) he
  let r := Classical.choose hex
  obtain ⟨hrs, hrt, hrf, hrfi, hrsm, hrism⟩ := Classical.choose_spec hex
  have hrf' (y : E3) : r y = (sphereDirection y, e * (‖y‖ - 1)) := by
    exact hrf y
  have hrfi' (p : UnitTwoSphere × ℝ) : r.symm p = (1 + e * p.2) • (p.1 : E3) := by
    exact hrfi p
  let QP := Q.prod (OpenPartialHomeomorph.refl ℝ)
  let R := QP.trans r.symm
  let D := nativeCapAmbientDiffeomorph ψ u tag
  let M := R.trans D.toHomeomorph.toOpenPartialHomeomorph
  let C := nativeCapRadialChart ψ u tag Q e he
  have hRs : R.source = Q.source ×ˢ Ioo (-1 : ℝ) 1 := by
    ext p
    change ((p.1 ∈ Q.source ∧ p.2 ∈ (univ : Set ℝ)) ∧
      (Q p.1, p.2) ∈ r.target) ↔ _
    rw [hrt]
    simp only [mem_prod, mem_univ, and_true, true_and]
  have hRt : R.target = {y : E3 | 0 < ‖y‖ ∧ ‖y‖ < 2 ∧
      sphereDirection y ∈ Q.target} := by
    ext y
    change (y ∈ r.source ∧ ((r y).1 ∈ Q.target ∧ (r y).2 ∈ (univ : Set ℝ))) ↔ _
    rw [hrs, hrf']
    simp only [mem_ofPred_eq, mem_univ, and_true, and_assoc]
  have hRf (p : E2 × ℝ) : R p = (1 + e * p.2) • (Q p.1 : E3) :=
    hrfi' (Q p.1, p.2)
  have hRfi (y : E3) : R.symm y = (Q.symm (sphereDirection y), e * (‖y‖ - 1)) := by
    change (Q.symm (r y).1, (r y).2) = _
    rw [hrf']
  have hQP : ContMDiffOn 𝓘(ℝ, E2 × ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ QP QP.source :=
    (hQ.comp contDiff_fst.contMDiff.contMDiffOn (fun _ hp => hp.1)).prodMk
      contDiff_snd.contMDiff.contMDiffOn
  have hQPi : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E2 × ℝ) ∞
      QP.symm QP.target :=
    (hQi.comp contMDiff_fst.contMDiffOn (fun _ hp => hp.1)).prodMk_space
      contMDiff_snd.contMDiffOn
  have hR : ContDiffOn ℝ ∞ R R.source :=
    (hrism.comp (hQP.mono inter_subset_left) (fun _ hp => hp.2)).contDiffOn
  have hRi : ContDiffOn ℝ ∞ R.symm R.target :=
    (hQPi.comp (hrsm.mono inter_subset_left) (fun _ hp => hp.2)).contDiffOn
  have hM : ContDiffOn ℝ ∞ M M.source :=
    D.contMDiff_toFun.contDiff.comp_contDiffOn (hR.mono inter_subset_left)
  have hMi : ContDiffOn ℝ ∞ M.symm M.target :=
    hRi.comp D.contMDiff_invFun.contDiff.contDiffOn (fun _ hp => hp.2)
  have hC : ContDiffOn ℝ ∞ C C.source :=
    tag.tube_smooth.comp (hM.mono inter_subset_left) (fun _ hp => hp.2)
  have hCi : ContDiffOn ℝ ∞ C.symm C.target :=
    hMi.comp (tag.tube_inverse.mono inter_subset_left) (fun _ hp => hp.2)
  have hCs : C.source = {p : E2 × ℝ | p.1 ∈ Q.source ∧ p.2 ∈ Ioo (-1) 1 ∧
      D ((1 + e * p.2) • (Q p.1 : E3)) ∈ tag.tube.source} := by
    ext p
    change ((p ∈ R.source ∧ R p ∈ (univ : Set E3)) ∧ D (R p) ∈ tag.tube.source) ↔ _
    rw [hRs, hRf]
    simp only [mem_prod, mem_ofPred_eq, mem_univ, and_true, and_assoc]
  have hCt : C.target = {Y : E3 | Y ∈ tag.tube.target ∧
      0 < ‖D.symm (tag.tube.symm Y)‖ ∧ ‖D.symm (tag.tube.symm Y)‖ < 2 ∧
      sphereDirection (D.symm (tag.tube.symm Y)) ∈ Q.target} := by
    ext Y
    change (Y ∈ tag.tube.target ∧ (tag.tube.symm Y ∈ (univ : Set (E2 × ℝ)) ∧
      D.symm (tag.tube.symm Y) ∈ R.target)) ↔ _
    rw [hRt]
    simp only [mem_univ, true_and, mem_ofPred_eq]
  have hCf (p : E2 × ℝ) : C p = tag.tube (D ((1 + e * p.2) • (Q p.1 : E3))) := by
    change tag.tube (D (R p)) = _
    rw [hRf]
  refine ⟨hCs, hCt, hCf, ?_, hC, hCi, ?_⟩
  · intro Y
    exact hRfi (D.symm (tag.tube.symm Y))
  · intro X hX
    obtain ⟨_, _, hDsphere, _⟩ := nativeCapAmbientDiffeomorph_spec ψ u tag
    have hDq := hDsphere (Q X)
    constructor
    · rw [hCs]
      refine ⟨hX, by norm_num, ?_⟩
      simpa only [mul_zero, add_zero, one_smul] using hDq.1
    · rw [hCf]
      simpa only [mul_zero, add_zero, one_smul] using hDq.2

end PoincareConjecture.M25.Topology3D
