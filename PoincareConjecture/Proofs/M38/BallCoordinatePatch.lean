import PoincareConjecture.Definitions.Ch15.SurgeryTopology
import Mathlib.Analysis.InnerProductSpace.Calculus









set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)


theorem surgeryBall_image_open : IsOpen (B.map '' Metric.ball 0 2) := by
  convert B.open_embedding.isOpen_range using 1
  ext y
  simp only [Set.mem_image, Set.mem_range, Subtype.exists]
  constructor <;> rintro ⟨z, hz, he⟩ <;> exact ⟨z, hz, he⟩


theorem surgeryBall_inverse_mem {x : A.carrier} (hx : x ∈ B.map '' Metric.ball 0 2) :
    B.inverse x ∈ Metric.ball 0 2 := by
  obtain ⟨z, hz, rfl⟩ := hx
  rwa [B.left_inverse hz]


theorem surgeryBall_closedImage_compact (r : ℝ) (hr : r < 2) :
    IsCompact (B.map '' Metric.closedBall 0 r) :=
  (isCompact_closedBall (0 : StandardCapSpace) r).image_of_continuousOn
    (B.map_smooth.continuousOn.mono (Metric.closedBall_subset_ball hr))


theorem surgeryBall_center_mem : B.map 0 ∈ B.closedBall := by
  exact Set.mem_image_of_mem B.map (by simp)


theorem surgeryBall_closedBall_subset_image : B.closedBall ⊆ B.map '' Metric.ball 0 2 :=
  Set.image_mono (Metric.closedBall_subset_ball (by norm_num))


theorem surgeryBall_mem_closedBall_iff {x : A.carrier}
    (hx : x ∈ B.map '' Metric.ball 0 2) :
    x ∈ B.closedBall ↔ ‖B.inverse x‖ ≤ 1 := by
  constructor
  · rintro ⟨z, hz, hzx⟩
    have hz' : z ∈ Metric.ball 0 2 := Metric.closedBall_subset_ball (by norm_num) hz
    have hcoord : B.inverse x = z := by rw [← hzx, B.left_inverse hz']
    rw [hcoord]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  · intro h
    exact ⟨B.inverse x, by simpa only [Metric.mem_closedBall, dist_zero_right] using h,
      B.right_inverse hx⟩


noncomputable def surgeryBallPatch (f : StandardCapSpace → StandardCapSpace) :
    A.carrier → A.carrier := by
  classical
  exact fun x => if x ∈ B.map '' Metric.ball 0 2 then B.map (f (B.inverse x)) else x


theorem surgeryBallPatch_of_mem (f : StandardCapSpace → StandardCapSpace)
    {x : A.carrier} (hx : x ∈ B.map '' Metric.ball 0 2) :
    surgeryBallPatch B f x = B.map (f (B.inverse x)) := by
  classical
  simp only [surgeryBallPatch, if_pos hx]


theorem surgeryBallPatch_of_not_mem (f : StandardCapSpace → StandardCapSpace)
    {x : A.carrier} (hx : x ∉ B.map '' Metric.ball 0 2) :
    surgeryBallPatch B f x = x := by
  classical
  simp only [surgeryBallPatch, if_neg hx]


theorem surgeryBallPatch_eq_self_off_compact (f : StandardCapSpace → StandardCapSpace)
    (hf : ∀ z, 3 / 2 ≤ ‖z‖ → f z = z)
    {x : A.carrier} (hx : x ∉ B.map '' Metric.closedBall 0 (3 / 2)) :
    surgeryBallPatch B f x = x := by
  by_cases hu : x ∈ B.map '' Metric.ball 0 2
  · have hnorm : 3 / 2 < ‖B.inverse x‖ := by
      by_contra! hn
      exact hx ⟨B.inverse x,
        by simpa only [Metric.mem_closedBall, dist_zero_right] using hn, B.right_inverse hu⟩
    rw [surgeryBallPatch_of_mem B f hu, hf _ hnorm.le, B.right_inverse hu]
  · exact surgeryBallPatch_of_not_mem B f hu



theorem surgeryBallPatch_smooth (f : StandardCapSpace → StandardCapSpace)
    {S : Set StandardCapSpace} (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S)
    (hmap : Set.MapsTo f S (Metric.ball 0 2))
    (houter : ∀ z, 3 / 2 ≤ ‖z‖ → f z = z)
    (D : Set A.carrier)
    (hD : ∀ x ∈ D, x ∈ B.map '' Metric.ball 0 2 → B.inverse x ∈ S) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (surgeryBallPatch B f) D := by
  have hfs : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f S := contMDiffOn_iff_contDiffOn.mpr hf
  intro x hx
  by_cases hu : x ∈ B.map '' Metric.ball 0 2
  · have hs : B.inverse x ∈ S := hD x hx hu
    have hi := B.inverse_smooth.contMDiffAt ((surgeryBall_image_open B).mem_nhds hu)
    have hmiddle := hfs.contMDiffAt (hS.mem_nhds hs)
    have hm := B.map_smooth.contMDiffAt (Metric.isOpen_ball.mem_nhds (hmap hs))
    have hcomp : ContMDiffAt (𝓡 3) (𝓡 3) ∞
        (fun y => B.map (f (B.inverse y))) x := hm.comp x (hmiddle.comp x hi)
    apply (hcomp.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [(surgeryBall_image_open B).mem_nhds hu] with y hy
    exact surgeryBallPatch_of_mem B f hy
  · have hk : x ∉ B.map '' Metric.closedBall 0 (3 / 2) := by
      intro hk
      exact hu ((Set.image_mono (Metric.closedBall_subset_ball (by norm_num))) hk)
    have hopen := (surgeryBall_closedImage_compact B (3 / 2) (by norm_num)).isClosed.isOpen_compl
    have hid : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (id : A.carrier → A.carrier) x := contMDiffAt_id
    apply (hid.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [hopen.mem_nhds hk] with y hy
    exact surgeryBallPatch_eq_self_off_compact B f houter hy

end PoincareConjecture.M38
