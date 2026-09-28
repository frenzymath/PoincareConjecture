import PoincareConjecture.Proofs.M38.FiniteCappingComparison
import PoincareConjecture.Proofs.M38.FiniteBallShrinking
import PoincareConjecture.Proofs.M38.CapAnnulus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem exists_finiteCappingDiffeomorph_of_germs
    {A D : GeneralizedSliceCarrier.{u}} {ι : Type*} [Finite ι]
    (B : ι → SurgeryBallEmbedding A) (C : ι → SurgeryBallEmbedding D)
    (E : SurgeryRegionEquivalence A D (⋃ i, (B i).closedBall)ᶜ
      (⋃ i, (C i).closedBall)ᶜ)
    (hB : ∀ i j, i ≠ j → Disjoint (B i).closedBall (B j).closedBall)
    (hC : ∀ i j, i ≠ j → Disjoint (C i).closedBall (C j).closedBall)
    (hmatch : ∀ i, ∃ r : ℝ, 0 < r ∧
      ∀ (z : UnitTwoSphere) (s : ℝ), 0 < s → s < r →
        E.map ((B i).map ((1 + s) • z.val)) = (C i).map ((1 + s) • z.val)) :
    ∃ d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier D.carrier ∞,
      (∀ y ∈ (⋃ i, (B i).closedBall)ᶜ, d y = E.map y) ∧
      ∀ i (z : StandardCapSpace), z ∈ Metric.closedBall 0 1 →
        d ((B i).map z) = (C i).map z := by
  classical
  obtain ⟨aB, haB, haB1, hsepB⟩ := exists_disjoint_surgeryBall_widths B hB
  obtain ⟨aC, haC, _, hsepC⟩ := exists_disjoint_surgeryBall_widths C hC
  choose r hr hmatch using hmatch
  let a : ι → ℝ := fun i => min (aB i) (min (aC i) (r i))
  have ha (i) : 0 < a i := lt_min (haB i) (lt_min (haC i) (hr i))
  have haB' (i) : a i ≤ aB i := min_le_left _ _
  have haC' (i) : a i ≤ aC i := (min_le_right _ _).trans (min_le_left _ _)
  have har (i) : a i ≤ r i := (min_le_right _ _).trans (min_le_right _ _)
  have ha1 (i) : a i < 1 := (haB' i).trans_lt (haB1 i)
  let B' := fun i => annulusReparametrizedBall (ha i) (ha1 i) (B i)
  let C' := fun i => annulusReparametrizedBall (ha i) (ha1 i) (C i)
  have hBeq : (⋃ i, (B' i).closedBall) = ⋃ i, (B i).closedBall :=
    iUnion_congr fun i => annulusReparametrizedBall_closedBall (ha i) (ha1 i) (B i)
  have hCeq : (⋃ i, (C' i).closedBall) = ⋃ i, (C i).closedBall :=
    iUnion_congr fun i => annulusReparametrizedBall_closedBall (ha i) (ha1 i) (C i)
  let E' : SurgeryRegionEquivalence A D (⋃ i, (B' i).closedBall)ᶜ
      (⋃ i, (C' i).closedBall)ᶜ := {
    map := E.map
    inverse := E.inverse
    map_image := by simpa only [hBeq, hCeq] using E.map_image
    inverse_image := by simpa only [hBeq, hCeq] using E.inverse_image
    left_inverse := by simpa only [hBeq] using E.left_inverse
    right_inverse := by simpa only [hCeq] using E.right_inverse
    map_smooth := by simpa only [hBeq] using E.map_smooth
    inverse_smooth := by simpa only [hCeq] using E.inverse_smooth }
  have hB' (i j : ι) (hij : i ≠ j) :
      Disjoint ((B' i).map '' Metric.ball 0 2) ((B' j).map '' Metric.ball 0 2) := by
    simp only [B', annulusReparametrizedBall_image]
    exact (hsepB i j hij).mono
      (image_mono (Metric.ball_subset_ball (by linarith [haB' i])))
      (image_mono (Metric.ball_subset_ball (by linarith [haB' j])))
  have hC' (i j : ι) (hij : i ≠ j) :
      Disjoint ((C' i).map '' Metric.ball 0 2) ((C' j).map '' Metric.ball 0 2) := by
    simp only [C', annulusReparametrizedBall_image]
    exact (hsepC i j hij).mono
      (image_mono (Metric.ball_subset_ball (by linarith [haC' i])))
      (image_mono (Metric.ball_subset_ball (by linarith [haC' j])))
  have hmatch' (i : ι) (z : StandardCapSpace) (hz : z ∈ Metric.ball 0 2)
      (hn : 1 < ‖z‖) : E'.map ((B' i).map z) = (C' i).map z := by
    have hn2 : ‖z‖ < 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hs : ‖z‖ - 1 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hrepr : z = (1 + (‖z‖ - 1)) • (capUnitDirection z).val :=
      (capAttachVector_coordinates z).symm
    have hBrep : (B' i).map z =
        (B i).map ((1 + a i * (‖z‖ - 1)) • (capUnitDirection z).val) :=
      (congrArg (B' i).map hrepr).trans
        (annulusReparametrizedBall_positive (ha i) (ha1 i) (B i) _ hs)
    have hCrep : (C' i).map z =
        (C i).map ((1 + a i * (‖z‖ - 1)) • (capUnitDirection z).val) :=
      (congrArg (C' i).map hrepr).trans
        (annulusReparametrizedBall_positive (ha i) (ha1 i) (C i) _ hs)
    change E.map ((B' i).map z) = (C' i).map z
    rw [hBrep, hCrep]
    exact hmatch i _ _ (mul_pos (ha i) hs.1)
      ((mul_lt_mul_of_pos_left hs.2 (ha i)).trans_le (by simpa using har i))
  let d := finiteCappingDiffeomorph B' C' E' hB' hC' hmatch'
  refine ⟨d, ?_, ?_⟩
  · intro y hy
    exact finiteCappingDiffeomorph_complement B' C' E' hB' hC' hmatch'
      (by simpa only [hBeq] using hy)
  · intro i z hz
    have hzimage : z ∈ capRadialDiffeomorph 1 (a i) (ha i) (ha1 i) ''
        Metric.closedBall 0 1 := by
      rw [capRadialDiffeomorph_closedBall]
      exact hz
    obtain ⟨w, hw, rfl⟩ := hzimage
    exact finiteCappingDiffeomorph_ball B' C' E' hB' hC' hmatch' i w
      (Metric.closedBall_subset_ball (by norm_num : (1 : ℝ) < 2) hw)

end PoincareConjecture.M38
