import PoincareConjecture.Proofs.M38.BallRegionTransport
import PoincareConjecture.Proofs.M38.SurgeryBallNeighborhood
import PoincareConjecture.Proofs.M38.SpherePunctureCoordinates
import PoincareConjecture.Proofs.M38.PartialHomeomorphRegions
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Diffeomorph.EssentialSphere.Extension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

attribute [local instance] threeManifoldLiftChartedSpace threeManifold_lift_isManifold

theorem cylinder_sphere_filling_or_collar_coordinates_of_source_eq
    (Q : GeneralizedSliceCarrier.{u})
    (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace Q.carrier ∞)
    (c : OpenPartialHomeomorph RoundCylinderSpace Q.carrier)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ) (hsource : c.source = univ ×ˢ Ioo (-δ) δ) :
    (∃ B : SurgeryBallEmbedding Q,
      frontier B.closedBall = range (fun z : UnitTwoSphere => c (z, 0))) ∨
    (∃ η : ℝ, 0 < η ∧ η < δ ∧
      ∃ D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace Q.carrier ∞,
        ∀ p : RoundCylinderSpace, |p.2| < η → D p = c p) := by
  classical
  let J := T.symm.trans Poincare.sphereCylinderDiffeomorphPunctured
  let C : PartialDiffeomorph CylModel (𝓡 3) RoundCylinderSpace Q.carrier ∞ := {
    toPartialEquiv := c.toPartialEquiv
    open_source := c.open_source
    open_target := c.open_target
    contMDiffOn_toFun := hc
    contMDiffOn_invFun := hci }
  let j₀ := T.symm.toPartialDiffeomorph.trans Poincare.radialPartialDiffeomorph
  have hj₀s : j₀.source = univ := by
    simp [j₀, PartialDiffeomorph.trans, Diffeomorph.toPartialDiffeomorph]
  have hj₀t : j₀.target = {0}ᶜ := by
    simp [j₀, PartialDiffeomorph.trans, Diffeomorph.toPartialDiffeomorph]
  let d := C.trans j₀
  have hds : d.source = c.source := by
    change c.source ∩ c ⁻¹' j₀.source = c.source
    rw [hj₀s]
    simp
  obtain ⟨F, hF⟩ := M38Schoenflies.Poincare.exists_ambient_map_of_euclidean_sphere_collar
    d.toOpenPartialHomeomorph d.contMDiffOn_toFun d.contMDiffOn_invFun hδ
    (hds.trans hsource)
  have hF0 (z : UnitTwoSphere) : F z.val ≠ 0 := by
    rw [hF z]
    exact (J (c (z, 0))).property
  by_cases hin : ‖F.symm 0‖ < 1
  · right
    obtain ⟨G, hG0, hGsphere⟩ := Poincare.exists_ambient_sphere_map_fixing_puncture F
      ⟨F.symm 0, by simpa only [Metric.mem_ball, dist_zero_right] using hin,
        F.apply_symm_apply 0⟩
    let H := (Poincare.sphereCylinderDiffeomorphPunctured.trans
      (Poincare.puncturedDiffeomorph G hG0)).trans J.symm
    have hH (z : UnitTwoSphere) : H (z, 0) = c (z, 0) := by
      apply J.injective
      apply Subtype.ext
      change (J (J.symm _)).val = (J (c (z, 0))).val
      rw [J.apply_symm_apply]
      change G (Poincare.sphereCylinderDiffeomorphPunctured (z, 0)).val = _
      rw [Poincare.sphereCylinderDiffeomorphPunctured_zero, hGsphere z.val z.property]
      exact hF z
    exact Poincare.exists_cylinder_extension_of_sphere_agreement
      hδ c hsource.symm.subset hc hci H hH
  · left
    have hout : 1 < ‖F.symm 0‖ := by
      apply lt_of_le_of_ne (le_of_not_gt hin)
      intro h
      let z : UnitTwoSphere := ⟨F.symm 0,
        by simpa only [Metric.mem_sphere, dist_zero_right] using h.symm⟩
      exact hF0 z (F.apply_symm_apply 0)
    let l : Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace euclideanCarrier.{u}.carrier ∞ := {
      toEquiv := (Homeomorph.ulift : euclideanCarrier.{u}.carrier ≃ₜ StandardCapSpace).symm.toEquiv
      contMDiff_toFun := threeManifold_up_contMDiff StandardCapSpace
      contMDiff_invFun := threeManifold_down_contMDiff StandardCapSpace }
    let a := F.trans l
    let B : SurgeryBallEmbedding euclideanCarrier.{u} := {
      map := a
      inverse := a.symm
      map_smooth := a.contMDiff.contMDiffOn
      inverse_smooth := a.symm.contMDiff.contMDiffOn
      left_inverse := fun _ _ => a.symm_apply_apply _
      right_inverse := fun _ _ => a.apply_symm_apply _
      open_embedding := a.toHomeomorph.isOpenEmbedding.comp Metric.isOpen_ball.isOpenEmbedding_subtypeVal }
    let j := j₀.trans l.toPartialDiffeomorph
    have hBs : B.closedBall ⊆ j.target := by
      rintro y ⟨z, hz, rfl⟩
      change l (F z) ∈ univ ∩ l.symm ⁻¹' j₀.target
      refine ⟨mem_univ _, ?_⟩
      rw [mem_preimage, l.symm_apply_apply, hj₀t]
      change F z ≠ 0
      intro hz0
      have hz' : z = F.symm 0 := by
        simpa only [F.symm_apply_apply] using congrArg F.symm hz0
      have hz1 : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      rw [hz'] at hz1
      exact hout.not_ge hz1
    obtain ⟨B', hB', _, hB's⟩ := exists_surgeryBall_with_image_in_open B j.open_target hBs
    let E := reverseRegions (partialHomeomorphRegions j.toOpenPartialHomeomorph
      j.contMDiffOn_toFun j.contMDiffOn_invFun)
    let D := transportSurgeryBallRegion B' E j.open_target j.open_source hB's
    refine ⟨D, ?_⟩
    have hfront : frontier D.closedBall = j.symm '' frontier B'.closedBall := by
      rw [surgeryBall_closedBall_frontier, surgeryBall_closedBall_frontier]
      change (j.symm ∘ B'.map) '' Metric.sphere 0 1 =
        j.symm '' (B'.map '' Metric.sphere 0 1)
      exact image_comp _ _ _
    rw [hfront, hB', surgeryBall_closedBall_frontier]
    apply subset_antisymm
    · rintro y ⟨w, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨⟨z, hz⟩, ?_⟩
      have heq : B.map z = j (c (⟨z, hz⟩, 0)) := congrArg l (hF ⟨z, hz⟩)
      change c (⟨z, hz⟩, 0) = j.symm (B.map z)
      rw [heq]
      exact (j.toPartialEquiv.left_inv (by
        change c (⟨z, hz⟩, 0) ∈ j₀.source ∩ j₀ ⁻¹' univ
        simp only [hj₀s, preimage_univ, inter_self, mem_univ])).symm
    · rintro y ⟨z, rfl⟩
      refine ⟨B.map z.val, ⟨z.val, z.property, rfl⟩, ?_⟩
      have heq : B.map z.val = j (c (z, 0)) := congrArg l (hF z)
      change j.symm (B.map z.val) = c (z, 0)
      rw [heq]
      exact j.toPartialEquiv.left_inv (by
        change c (z, 0) ∈ j₀.source ∩ j₀ ⁻¹' univ
        simp only [hj₀s, preimage_univ, inter_self, mem_univ])

theorem cylinder_sphere_filling_or_collar_coordinates
    (Q : GeneralizedSliceCarrier.{u})
    (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace Q.carrier ∞)
    (c : OpenPartialHomeomorph RoundCylinderSpace Q.carrier)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ) (hsource : univ ×ˢ Ioo (-δ) δ ⊆ c.source) :
    (∃ B : SurgeryBallEmbedding Q,
      frontier B.closedBall = range (fun z : UnitTwoSphere => c (z, 0))) ∨
    (∃ η : ℝ, 0 < η ∧ η < δ ∧
      ∃ D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace Q.carrier ∞,
        ∀ p : RoundCylinderSpace, |p.2| < η → D p = c p) := by
  let V : Set RoundCylinderSpace := univ ×ˢ Ioo (-δ) δ
  let d := c.restr V
  have hV : IsOpen V := isOpen_univ.prod isOpen_Ioo
  have hds : d.source = V :=
    (c.restr_source' V hV).trans (inter_eq_right.mpr hsource)
  exact cylinder_sphere_filling_or_collar_coordinates_of_source_eq Q T d
    (hc.mono (fun _ h => h.1)) (hci.mono (fun _ h => h.1)) hδ hds

end PoincareConjecture.M38
