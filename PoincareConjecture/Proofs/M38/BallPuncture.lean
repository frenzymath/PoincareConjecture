import PoincareConjecture.Proofs.M38.BallCoordinatePatch
import PoincareConjecture.Proofs.M38.PunctureRadial

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem punctureCollapse_mem_ball {x : StandardCapSpace}
    (hx : 1 < ‖x‖) (hupper : ‖x‖ < 2) : punctureCollapse x ∈ Metric.ball 0 2 := by
  rw [Metric.mem_ball, dist_zero_right, punctureCollapse_norm hx]
  calc
    punctureRadialOrderIso ‖x‖ < punctureRadialOrderIso 2 :=
      punctureRadialOrderIso.strictMono hupper
    _ = 2 := punctureRadialOrderIso_eq_self 2 (by norm_num)

theorem punctureExpand_mem_ball {x : StandardCapSpace}
    (hx : 0 < ‖x‖) (hupper : ‖x‖ < 2) : punctureExpand x ∈ Metric.ball 0 2 := by
  rw [Metric.mem_ball, dist_zero_right, punctureExpand_norm hx]
  calc
    punctureRadialOrderIso.symm ‖x‖ < punctureRadialOrderIso.symm 2 :=
      punctureRadialOrderIso.symm.strictMono hupper
    _ = 2 := punctureRadialOrderIso_symm_eq_self 2 (by norm_num)

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)

theorem surgeryBall_exterior_coordinates {x : A.carrier}
    (hx : x ∈ B.closedBallᶜ) (hu : x ∈ B.map '' Metric.ball 0 2) :
    1 < ‖B.inverse x‖ ∧ ‖B.inverse x‖ < 2 := by
  constructor
  · exact lt_of_not_ge (fun h => hx ((surgeryBall_mem_closedBall_iff B hu).mpr h))
  · simpa only [Metric.mem_ball, dist_zero_right] using surgeryBall_inverse_mem B hu

theorem surgeryBall_puncture_coordinates {x : A.carrier}
    (hx : x ∈ ({B.map 0} : Set A.carrier)ᶜ) (hu : x ∈ B.map '' Metric.ball 0 2) :
    0 < ‖B.inverse x‖ ∧ ‖B.inverse x‖ < 2 := by
  constructor
  · apply norm_pos_iff.mpr
    intro hzero
    apply hx
    change x = B.map 0
    rw [← B.right_inverse hu, hzero]
  · simpa only [Metric.mem_ball, dist_zero_right] using surgeryBall_inverse_mem B hu

noncomputable def surgeryBallCollapse : A.carrier → A.carrier :=
  surgeryBallPatch B punctureCollapse

noncomputable def surgeryBallExpand : A.carrier → A.carrier :=
  surgeryBallPatch B punctureExpand

theorem surgeryBallCollapse_map {z : StandardCapSpace} (hz : z ∈ Metric.ball 0 2) :
    surgeryBallCollapse B (B.map z) = B.map (punctureCollapse z) := by
  rw [surgeryBallCollapse, surgeryBallPatch_of_mem B _ (Set.mem_image_of_mem _ hz),
    B.left_inverse hz]

theorem surgeryBallExpand_map {z : StandardCapSpace} (hz : z ∈ Metric.ball 0 2) :
    surgeryBallExpand B (B.map z) = B.map (punctureExpand z) := by
  rw [surgeryBallExpand, surgeryBallPatch_of_mem B _ (Set.mem_image_of_mem _ hz),
    B.left_inverse hz]

theorem surgeryBallCollapse_mapsTo :
    Set.MapsTo (surgeryBallCollapse B) B.closedBallᶜ ({B.map 0} : Set A.carrier)ᶜ := by
  intro x hx
  by_cases hu : x ∈ B.map '' Metric.ball 0 2
  · obtain ⟨hpos, hupper⟩ := surgeryBall_exterior_coordinates B hx hu
    have hc := punctureCollapse_mem_ball hpos hupper
    rw [surgeryBallCollapse, surgeryBallPatch_of_mem B _ hu]
    intro heq
    have hcoord := congrArg B.inverse (show B.map (punctureCollapse (B.inverse x)) =
      B.map 0 from heq)
    rw [B.left_inverse hc, B.left_inverse (by simp)] at hcoord
    have hn : 0 < ‖punctureCollapse (B.inverse x)‖ := by
      rw [punctureCollapse_norm hpos]
      exact (punctureRadialOrderIso_pos_iff _).mpr hpos
    simp only [hcoord, norm_zero, lt_self_iff_false] at hn
  · rw [surgeryBallCollapse, surgeryBallPatch_of_not_mem B _ hu]
    intro heq
    exact hx (heq ▸ surgeryBall_center_mem B)

theorem surgeryBallExpand_mapsTo :
    Set.MapsTo (surgeryBallExpand B) ({B.map 0} : Set A.carrier)ᶜ B.closedBallᶜ := by
  intro x hx
  by_cases hu : x ∈ B.map '' Metric.ball 0 2
  · obtain ⟨hpos, hupper⟩ := surgeryBall_puncture_coordinates B hx hu
    have he := punctureExpand_mem_ball hpos hupper
    rw [surgeryBallExpand, surgeryBallPatch_of_mem B _ hu]
    intro hclosed
    have hn := (surgeryBall_mem_closedBall_iff B (Set.mem_image_of_mem _ he)).mp hclosed
    rw [B.left_inverse he, punctureExpand_norm hpos] at hn
    exact (not_le_of_gt (punctureRadialOrderIso_symm_gt_one hpos)) hn
  · rw [surgeryBallExpand, surgeryBallPatch_of_not_mem B _ hu]
    exact fun hclosed => hu (surgeryBall_closedBall_subset_image B hclosed)

theorem surgeryBallExpand_collapse :
    Set.LeftInvOn (surgeryBallExpand B) (surgeryBallCollapse B) B.closedBallᶜ := by
  intro x hx
  by_cases hu : x ∈ B.map '' Metric.ball 0 2
  · obtain ⟨hpos, hupper⟩ := surgeryBall_exterior_coordinates B hx hu
    calc
      surgeryBallExpand B (surgeryBallCollapse B x) =
          surgeryBallExpand B (B.map (punctureCollapse (B.inverse x))) :=
        congrArg (surgeryBallExpand B) (surgeryBallPatch_of_mem B _ hu)
      _ = B.map (punctureExpand (punctureCollapse (B.inverse x))) :=
        surgeryBallExpand_map B (punctureCollapse_mem_ball hpos hupper)
      _ = B.map (B.inverse x) := congrArg B.map (punctureExpand_collapse hpos)
      _ = x := B.right_inverse hu
  · rw [surgeryBallCollapse, surgeryBallPatch_of_not_mem B _ hu,
      surgeryBallExpand, surgeryBallPatch_of_not_mem B _ hu]

theorem surgeryBallCollapse_expand :
    Set.LeftInvOn (surgeryBallCollapse B) (surgeryBallExpand B)
      ({B.map 0} : Set A.carrier)ᶜ := by
  intro x hx
  by_cases hu : x ∈ B.map '' Metric.ball 0 2
  · obtain ⟨hpos, hupper⟩ := surgeryBall_puncture_coordinates B hx hu
    calc
      surgeryBallCollapse B (surgeryBallExpand B x) =
          surgeryBallCollapse B (B.map (punctureExpand (B.inverse x))) :=
        congrArg (surgeryBallCollapse B) (surgeryBallPatch_of_mem B _ hu)
      _ = B.map (punctureCollapse (punctureExpand (B.inverse x))) :=
        surgeryBallCollapse_map B (punctureExpand_mem_ball hpos hupper)
      _ = B.map (B.inverse x) := congrArg B.map (punctureCollapse_expand hpos)
      _ = x := B.right_inverse hu
  · rw [surgeryBallExpand, surgeryBallPatch_of_not_mem B _ hu,
      surgeryBallCollapse, surgeryBallPatch_of_not_mem B _ hu]

theorem surgeryBallCollapse_smooth :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (surgeryBallCollapse B) B.closedBallᶜ := by
  apply surgeryBallPatch_smooth B punctureCollapse
    (S := {z | 1 < ‖z‖ ∧ ‖z‖ < 2})
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const))
    (punctureCollapse_smooth.mono (fun _ h => h.1))
    (fun _ h => punctureCollapse_mem_ball h.1 h.2)
    (fun _ h => punctureCollapse_eq_self h)
  exact fun _ hx hu => surgeryBall_exterior_coordinates B hx hu

theorem surgeryBallExpand_smooth :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (surgeryBallExpand B) ({B.map 0} : Set A.carrier)ᶜ := by
  apply surgeryBallPatch_smooth B punctureExpand
    (S := {z | 0 < ‖z‖ ∧ ‖z‖ < 2})
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const))
    (punctureExpand_smooth.mono (fun _ h => h.1))
    (fun _ h => punctureExpand_mem_ball h.1 h.2)
    (fun _ h => punctureExpand_eq_self h)
  exact fun _ hx hu => surgeryBall_puncture_coordinates B hx hu

noncomputable def surgeryBallPunctureEquivalence :
    SurgeryRegionEquivalence A A B.closedBallᶜ ({B.map 0} : Set A.carrier)ᶜ where
  map := surgeryBallCollapse B
  inverse := surgeryBallExpand B
  map_image := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact surgeryBallCollapse_mapsTo B hx
    · intro y hy
      exact ⟨surgeryBallExpand B y, surgeryBallExpand_mapsTo B hy,
        surgeryBallCollapse_expand B hy⟩
  inverse_image := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact surgeryBallExpand_mapsTo B hx
    · intro y hy
      exact ⟨surgeryBallCollapse B y, surgeryBallCollapse_mapsTo B hy,
        surgeryBallExpand_collapse B hy⟩
  left_inverse := surgeryBallExpand_collapse B
  right_inverse := surgeryBallCollapse_expand B
  map_smooth := surgeryBallCollapse_smooth B
  inverse_smooth := surgeryBallExpand_smooth B

end PoincareConjecture.M38
