import PoincareConjecture.Proofs.M38.CollaredChartFilling
import PoincareConjecture.Proofs.M38.ProjectiveCutIdentification
import PoincareConjecture.Proofs.M38.ShortCollarConnectedSum












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38



theorem exists_projectiveDouble_first_filled_side
    (A : GeneralizedSliceCarrier.{u}) (C : SmoothProjectiveDoubleModel A.carrier) :
    ∃ (r : ℝ) (D : SurgeryBallEmbedding projectiveCarrier.{u})
      (E : SurgeryRegionEquivalence projectiveCarrier.{u} A
        D.closedBallᶜ C.first_region),
      0 < r ∧ r < 1 / 2 ∧
      ∀ (z : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-r) 0 →
        C.collar (z, s) = E.map (D.map ((1 - s) • z.val)) := by
  let p : projectiveCarrier.{u}.carrier := ULift.up C.first_puncture
  let e := chartAt StandardCapSpace p
  obtain ⟨H, K, δ, c, hK, hKs, hKreg, hKcomp, hHU, hδ, hcs, hct,
      hc, hci, hfront, hside, hformula⟩ :=
    exists_projectiveDouble_first_cut_collar A C e.open_source (mem_chart_source _ p)
  obtain ⟨r, D, hr, hrhalf, hD, _, hmatch⟩ :=
    exists_surgeryBall_of_collared_coordinate_domain e
      contMDiffOn_chart contMDiffOn_chart_symm hK hKs hKreg c hc hci
      hδ hcs.symm.subset hct hfront hside
  have hDcomp : D.closedBallᶜ =
      (puncturedProjectiveRegionEquivalence A C.first_model).inverse ''
        (H '' C.first_region) := by rw [hD]; exact hKcomp
  let E := interiorCutRegionEquivalence
    (puncturedProjectiveRegionEquivalence A C.first_model) H
    ((image_mono subset_closure).trans hHU) hDcomp
  refine ⟨r, D, E, hr, hrhalf, ?_⟩
  apply projectiveCut_negative_gluing A C H hHU D hDcomp (by linarith)
  intro z s hs
  rw [hmatch z s hs, hformula]



theorem exists_projectiveDouble_second_filled_side
    (A : GeneralizedSliceCarrier.{u}) (C : SmoothProjectiveDoubleModel A.carrier) :
    ∃ (r : ℝ) (D : SurgeryBallEmbedding projectiveCarrier.{u})
      (E : SurgeryRegionEquivalence projectiveCarrier.{u} A
        D.closedBallᶜ C.second_region),
      0 < r ∧ r < 1 / 2 ∧
      ∀ (z : UnitTwoSphere) (s : ℝ), s ∈ Ioo (0 : ℝ) r →
        C.collar (z, s) = E.map (D.map ((1 + s) • z.val)) := by
  obtain ⟨r, D, E, hr, hrhalf, hmatch⟩ :=
    exists_projectiveDouble_first_filled_side A (reverseProjectiveDouble C)
  refine ⟨r, D, E, hr, hrhalf, ?_⟩
  intro z s hs
  have h := hmatch z (-s) (by constructor <;> linarith [hs.1, hs.2])
  change C.collar (z, - -s) = E.map (D.map ((1 - -s) • z.val)) at h
  simpa only [neg_neg, sub_neg_eq_add] using h




theorem exists_projectiveDouble_connectedSum
    (A : GeneralizedSliceCarrier.{u}) (C : SmoothProjectiveDoubleModel A.carrier) :
    Nonempty (SmoothConnectedSumData projectiveCarrier.{u} projectiveCarrier.{u} A) := by
  obtain ⟨r, D₀, E₀, hr, hrhalf, hnegative⟩ :=
    exists_projectiveDouble_first_filled_side A C
  obtain ⟨s, D₁, E₁, hs, _, hpositive⟩ :=
    exists_projectiveDouble_second_filled_side A C
  let ε := min r s
  have hε : 0 < ε := lt_min hr hs
  have hεone : ε ≤ 1 := (min_le_left _ _).trans (by linarith)
  let original := projectiveDoubleCollarChart C
  let b := original.toOpenPartialHomeomorph.restrOpen
    (univ ×ˢ Ioo (-ε) ε) (isOpen_univ.prod isOpen_Ioo)
  let c : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      RoundCylinderSpace A.carrier ∞ := {
    toPartialEquiv := b.toPartialEquiv
    open_source := b.open_source
    open_target := b.open_target
    contMDiffOn_toFun := original.contMDiffOn_toFun.mono inter_subset_left
    contMDiffOn_invFun := original.contMDiffOn_invFun.mono inter_subset_left }
  have hc : c.source = univ ×ˢ Ioo (-ε) ε := by
    apply inter_eq_right.mpr
    intro z hz
    exact ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hcentral : c '' (univ ×ˢ ({0} : Set ℝ)) = C.sphere := C.collar_sphere
  apply exists_connectedSumData_of_local_gluing D₀ D₁ C.first_open C.second_open
    E₀ E₁ C.disjoint (Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞) c hc
    (fun z t ht => hnegative z t
      ⟨by have := min_le_left r s; linarith [ht.1], ht.2⟩)
    (fun z t ht => hpositive z t ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩)
    (hcentral.symm ▸ C.sphere_disjoint) (hcentral.symm ▸ C.cover) hε

end PoincareConjecture.M38
