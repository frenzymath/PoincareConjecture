import PoincareConjecture.Proofs.M38.ReciprocalBallAnnuli










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A : GeneralizedSliceCarrier.{u}} (C : SurgeryBallEmbedding A)
  {a : ℝ} (ha : 0 < a) (ha8 : a ≤ 1 / 8)


noncomputable def reciprocalEnclosingBall : SurgeryBallEmbedding A := by
  let e := reciprocalInnerBallDiffeomorph ha ha8
  let f := C.map ∘ e
  let g := e.symm ∘ C.inverse
  have hmaps : Set.MapsTo e (Metric.ball 0 2) (Metric.ball 0 2) :=
    reciprocalInnerBallDiffeomorph_mapsTo ha ha8
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (Metric.ball 0 2) :=
    C.map_smooth.comp e.contMDiff.contMDiffOn hmaps
  have hsub : f '' Metric.ball 0 2 ⊆ C.map '' Metric.ball 0 2 := by
    rintro _ ⟨x, hx, rfl⟩
    exact Set.mem_image_of_mem _ (hmaps hx)
  have hg : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g (f '' Metric.ball 0 2) :=
    e.symm.contMDiff.comp_contMDiffOn (C.inverse_smooth.mono hsub)
  have hleft : Set.LeftInvOn g f (Metric.ball 0 2) := by
    intro x hx
    change e.symm (C.inverse (C.map (e x))) = x
    rw [C.left_inverse (hmaps hx), e.symm_apply_apply]
  exact {
    map := f
    inverse := g
    map_smooth := hf
    inverse_smooth := hg
    left_inverse := hleft
    right_inverse := by
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg f (hleft hx)
    open_embedding := smooth_left_inverse_openEmbedding Metric.isOpen_ball hf hg hleft }


theorem reciprocalEnclosingBall_map (x : StandardCapSpace) :
    (reciprocalEnclosingBall C ha ha8).map x =
      C.map (reciprocalInnerBallDiffeomorph ha ha8 x) := rfl


theorem reciprocalEnclosingBall_inverse (y : A.carrier) :
    (reciprocalEnclosingBall C ha ha8).inverse y =
      (reciprocalInnerBallDiffeomorph ha ha8).symm (C.inverse y) := rfl


theorem reciprocalEnclosingBall_full_bound :
    (reciprocalEnclosingBall C ha ha8).map '' Metric.ball 0 2 ⊆
      C.map '' Metric.ball 0 (45 / 28) := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨reciprocalInnerBallDiffeomorph ha ha8 x, ?_, rfl⟩
  simpa only [Metric.mem_ball, dist_zero_right] using
    reciprocalInnerBallDiffeomorph_bound ha ha8 hx


theorem reciprocalEnclosingBall_full_inside :
    (reciprocalEnclosingBall C ha ha8).map '' Metric.ball 0 2 ⊆
      C.map '' Metric.ball 0 2 :=
  (reciprocalEnclosingBall_full_bound C ha ha8).trans
    (Set.image_mono (Metric.ball_subset_ball (by norm_num)))


theorem reciprocalEnclosingBall_closedBall :
    (reciprocalEnclosingBall C ha ha8).closedBall =
      C.map '' Metric.closedBall 0 (3 / 2) := by
  change (C.map ∘ reciprocalInnerBallDiffeomorph ha ha8) '' Metric.closedBall 0 1 = _
  rw [Set.image_comp, reciprocalInnerBallDiffeomorph_closedBall]


theorem reciprocalEnclosingBall_center :
    (reciprocalEnclosingBall C ha ha8).map 0 = C.map 0 := by
  rw [reciprocalEnclosingBall_map]
  apply congrArg C.map
  apply norm_eq_zero.mp
  rw [reciprocalInnerBallDiffeomorph_norm]
  simp


theorem reciprocalEnclosingBall_mem_closedBall_iff {y : A.carrier}
    (hy : y ∈ C.map '' Metric.ball 0 2) :
    y ∈ (reciprocalEnclosingBall C ha ha8).closedBall ↔ ‖C.inverse y‖ ≤ 3 / 2 := by
  rw [reciprocalEnclosingBall_closedBall]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [C.left_inverse (Metric.closedBall_subset_ball (by norm_num) hx)]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  · intro hnorm
    exact ⟨C.inverse y, by simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm,
      C.right_inverse hy⟩


theorem reciprocalEnclosingBall_contains_unit :
    C.map '' Metric.ball 0 1 ⊆ (reciprocalEnclosingBall C ha ha8).closedBall := by
  rw [reciprocalEnclosingBall_closedBall]
  exact Set.image_mono (Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall (by norm_num)))


theorem reciprocalEnclosingBall_negative (z : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Set.Ioo (-1 : ℝ) 0) :
    (reciprocalEnclosingBall C ha ha8).map ((1 - s) • z.val) =
      C.map (((3 / 2) * ((1 + a * s / 2) / (1 + a * s))) • z.val) := by
  rw [reciprocalEnclosingBall_map, reciprocalInnerBallDiffeomorph_negative ha ha8 z hs]

end PoincareConjecture.M38
