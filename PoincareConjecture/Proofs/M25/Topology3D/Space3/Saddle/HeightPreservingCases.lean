import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HeightPreservingData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HeightPreservingSlice
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BallTransport










set_option autoImplicit false

open Set
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞



noncomputable def SaddleLowerLevelData.mapHeightPreserving
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    {D : SaddlePieceData psi u}
    (W : SaddleLowerLevelData D) (K : D3)
    (hK : ∀ y : E3, ⟪(u : E3), K y⟫_ℝ = ⟪(u : E3), y⟫_ℝ) :
    SaddleLowerLevelData (D.mapHeightPreserving K hK) := by
  let F := heightPreservingSliceDiffeomorph u K hK W.level
  have hrec := (heightPreservingSliceDiffeomorph_geometry u K hK).2.2.2.1
  exact {
    level := W.level
    level_lt_critical := by
      change W.level < ⟪(u : E3), K (psi (D.point, 0))⟫_ℝ
      rw [hK]
      exact W.level_lt_critical
    lower_seams_lt_level := W.lower_seams_lt_level
    label := W.label
    label_injective := W.label_injective
    label_lower := W.label_lower
    leg := W.leg
    leg_source := W.leg_source
    leg_smooth := W.leg_smooth
    leg_inverse := W.leg_inverse
    leg_height := by simpa only [hK] using W.leg_height
    leg_bottom := W.leg_bottom
    leg_disjoint := W.leg_disjoint
    leg_cover := by
      change (⋃ b, W.leg b '' (univ ×ˢ Icc
        ((D.cap (W.label b)).cutHeight + (D.cap (W.label b)).sign *
          (D.cap (W.label b)).removal) W.level)) =
        D.sourceCore ∩ {q | ⟪(u : E3), K (psi (q, 0))⟫_ℝ ≤ W.level}
      simpa only [hK] using W.leg_cover
    disc := fun b => (W.disc b).mapDiffeomorph F
    disc_boundary := by
      intro b
      change (fun x => (heightPlaneCoordinates u).symm (x, W.level)) ''
        ((W.disc b).mapDiffeomorph F).boundary =
        range (fun theta => K (psi (W.leg b (theta, W.level), 0)))
      rw [BallNeighborhoodChart.mapDiffeomorph_boundary, image_image]
      calc
        _ = (fun x => K ((heightPlaneCoordinates u).symm (x, W.level))) ''
            (W.disc b).boundary := image_congr (fun x _ => (hrec W.level x).symm)
        _ = K '' ((fun x => (heightPlaneCoordinates u).symm (x, W.level)) ''
            (W.disc b).boundary) := (image_image _ _ _).symm
        _ = K '' range (fun theta => psi (W.leg b (theta, W.level), 0)) := by
          rw [W.disc_boundary b]
        _ = _ := (range_comp' _ _).symm }




theorem SaddleLowerLevelData.mapHeightPreserving_geometry
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    {D : SaddlePieceData psi u}
    (W : SaddleLowerLevelData D) (K : D3)
    (hK : ∀ y : E3, ⟪(u : E3), K y⟫_ℝ = ⟪(u : E3), y⟫_ℝ) :
    let W' := W.mapHeightPreserving K hK
    let F := heightPreservingSliceDiffeomorph u K hK W.level
    W'.level = W.level ∧ W'.label = W.label ∧ W'.leg = W.leg ∧
    (∀ b : Fin 2, W'.disc b = (W.disc b).mapDiffeomorph F) ∧
    (Disjoint (W'.disc 0).closedRegion (W'.disc 1).closedRegion ↔
      Disjoint (W.disc 0).closedRegion (W.disc 1).closedRegion) ∧
    (((W'.disc 0).closedRegion ⊆ (W'.disc 1).inside ∨
      (W'.disc 1).closedRegion ⊆ (W'.disc 0).inside) ↔
      ((W.disc 0).closedRegion ⊆ (W.disc 1).inside ∨
        (W.disc 1).closedRegion ⊆ (W.disc 0).inside)) := by
  let F := heightPreservingSliceDiffeomorph u K hK W.level
  have hFinj : Function.Injective (fun x : E2 => F x) := F.injective
  have himg (s t : Set E2) :
      ((F : E2 → E2) '' s ⊆ (F : E2 → E2) '' t) ↔ s ⊆ t :=
    Set.image_subset_image_iff F.injective
  refine ⟨rfl, rfl, rfl, fun _ => rfl, ?_, ?_⟩
  · change Disjoint ((W.disc 0).mapDiffeomorph F).closedRegion
      ((W.disc 1).mapDiffeomorph F).closedRegion ↔ _
    rw [BallNeighborhoodChart.mapDiffeomorph_closedRegion,
      BallNeighborhoodChart.mapDiffeomorph_closedRegion]
    exact Set.disjoint_image_iff hFinj
  · change (((W.disc 0).mapDiffeomorph F).closedRegion ⊆
      ((W.disc 1).mapDiffeomorph F).inside ∨
      ((W.disc 1).mapDiffeomorph F).closedRegion ⊆ ((W.disc 0).mapDiffeomorph F).inside) ↔ _
    rw [BallNeighborhoodChart.mapDiffeomorph_closedRegion,
      BallNeighborhoodChart.mapDiffeomorph_inside,
      BallNeighborhoodChart.mapDiffeomorph_closedRegion,
      BallNeighborhoodChart.mapDiffeomorph_inside]
    constructor
    · intro h
      rcases h with h | h
      · exact Or.inl ((himg (W.disc 0).closedRegion (W.disc 1).inside).mp h)
      · exact Or.inr ((himg (W.disc 1).closedRegion (W.disc 0).inside).mp h)
    · intro h
      rcases h with h | h
      · exact Or.inl ((himg (W.disc 0).closedRegion (W.disc 1).inside).mpr h)
      · exact Or.inr ((himg (W.disc 1).closedRegion (W.disc 0).inside).mpr h)




theorem SaddlePieceData.mapHeightPreserving_cases
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (D : SaddlePieceData psi u) (K : D3)
    (hK : ∀ y : E3, ⟪(u : E3), K y⟫_ℝ = ⟪(u : E3), y⟫_ℝ) :
    let D' := D.mapHeightPreserving K hK
    (D'.nonnested ↔ D.nonnested) ∧ (D'.nested ↔ D.nested) := by
  let D' := D.mapHeightPreserving K hK
  have hKi := (heightPreservingSliceDiffeomorph_geometry u K hK).1
  have hrec := (heightPreservingSliceDiffeomorph_geometry u K.symm hKi).2.2.2.1
  let back (V : SaddleLowerLevelData D') : SaddleLowerLevelData D := {
    level := V.level
    level_lt_critical := by
      have hv := V.level_lt_critical
      change V.level < ⟪(u : E3), K (psi (D.point, 0))⟫_ℝ at hv
      rw [hK] at hv
      exact hv
    lower_seams_lt_level := V.lower_seams_lt_level
    label := V.label
    label_injective := V.label_injective
    label_lower := V.label_lower
    leg := V.leg
    leg_source := V.leg_source
    leg_smooth := V.leg_smooth
    leg_inverse := V.leg_inverse
    leg_height := by simpa only [hK] using V.leg_height
    leg_bottom := V.leg_bottom
    leg_disjoint := V.leg_disjoint
    leg_cover := by
      simpa only [D', SaddlePieceData.mapHeightPreserving,
        SurgeryCapTag.mapHeightPreserving, hK] using V.leg_cover
    disc := fun b => (V.disc b).mapDiffeomorph
      (heightPreservingSliceDiffeomorph u K.symm hKi V.level)
    disc_boundary := by
      intro b
      let G := heightPreservingSliceDiffeomorph u K.symm hKi V.level
      change (fun x => (heightPlaneCoordinates u).symm (x, V.level)) ''
        ((V.disc b).mapDiffeomorph G).boundary =
        range (fun theta => psi (V.leg b (theta, V.level), 0))
      rw [BallNeighborhoodChart.mapDiffeomorph_boundary, image_image]
      calc
        _ = (fun x => K.symm ((heightPlaneCoordinates u).symm (x, V.level))) ''
            (V.disc b).boundary := image_congr (fun x _ => (hrec V.level x).symm)
        _ = K.symm '' ((fun x => (heightPlaneCoordinates u).symm (x, V.level)) ''
            (V.disc b).boundary) := (image_image _ _ _).symm
        _ = K.symm '' range (fun theta => K (psi (V.leg b (theta, V.level), 0))) := by
          rw [V.disc_boundary b]
        _ = _ := by rw [← range_comp']; simp only [K.symm_apply_apply] }
  constructor
  · constructor
    · rintro ⟨V, hV⟩
      refine ⟨back V, ?_⟩
      change Disjoint ((V.disc 0).mapDiffeomorph _).closedRegion
        ((V.disc 1).mapDiffeomorph _).closedRegion
      rw [BallNeighborhoodChart.mapDiffeomorph_closedRegion,
        BallNeighborhoodChart.mapDiffeomorph_closedRegion]
      exact disjoint_image_of_injective
        (heightPreservingSliceDiffeomorph u K.symm hKi V.level).injective hV
    · rintro ⟨W, hW⟩
      refine ⟨W.mapHeightPreserving K hK, ?_⟩
      exact (W.mapHeightPreserving_geometry K hK).2.2.2.2.1.mpr hW
  · constructor
    · rintro ⟨V, hV⟩
      refine ⟨back V, ?_⟩
      change ((V.disc 0).mapDiffeomorph _).closedRegion ⊆
        ((V.disc 1).mapDiffeomorph _).inside ∨
        ((V.disc 1).mapDiffeomorph _).closedRegion ⊆ ((V.disc 0).mapDiffeomorph _).inside
      simp only [BallNeighborhoodChart.mapDiffeomorph_closedRegion,
        BallNeighborhoodChart.mapDiffeomorph_inside]
      exact hV.imp image_mono image_mono
    · rintro ⟨W, hW⟩
      refine ⟨W.mapHeightPreserving K hK, ?_⟩
      exact (W.mapHeightPreserving_geometry K hK).2.2.2.2.2.mpr hW

end PoincareConjecture.M25.Topology3D
