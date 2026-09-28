import PoincareConjecture.Proofs.M38.NormalRadialExpansion
import PoincareConjecture.Proofs.M38.BallNeighborhood










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38

variable {A : GeneralizedSliceCarrier.{u}} {a : ℝ}
  (ha : 0 < a) (ha1 : a < 1) (B : SurgeryBallEmbedding A)



noncomputable def normalCorrectedBall : SurgeryBallEmbedding A := by
  let e := normalRadialExpansion ha ha1
  let f := B.map ∘ e
  let g := e.symm ∘ B.inverse
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (Metric.ball 0 2) :=
    B.map_smooth.comp e.contMDiff.contMDiffOn (normalRadialExpansion_mapsTo ha ha1)
  have hsub : f '' Metric.ball 0 2 ⊆ B.map '' Metric.ball 0 2 := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_image_of_mem _ (normalRadialExpansion_mapsTo ha ha1 hx)
  have hg : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g (f '' Metric.ball 0 2) :=
    e.symm.contMDiff.comp_contMDiffOn (B.inverse_smooth.mono hsub)
  have hleft : LeftInvOn g f (Metric.ball 0 2) := by
    intro x hx
    change e.symm (B.inverse (B.map (e x))) = x
    rw [B.left_inverse (normalRadialExpansion_mapsTo ha ha1 hx), e.symm_apply_apply]
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

theorem normalCorrectedBall_closedBall :
    (normalCorrectedBall ha ha1 B).closedBall = B.closedBall := by
  change (B.map ∘ normalRadialExpansion ha ha1) '' Metric.closedBall 0 1 = _
  rw [image_comp, normalRadialExpansion_closedBall]
  rfl

theorem normalCorrectedBall_image_subset :
    (normalCorrectedBall ha ha1 B).map '' Metric.ball 0 2 ⊆
      B.map '' Metric.ball 0 2 := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨normalRadialExpansion ha ha1 x, normalRadialExpansion_mapsTo ha ha1 hx, rfl⟩

theorem normalCorrectedBall_annulus (z : UnitTwoSphere) {s : ℝ} (hs : |s| ≤ a / 8) :
    (normalCorrectedBall ha ha1 B).map ((1 + s) • z.val) =
      B.map ((1 + s / a) • z.val) := by
  change B.map (normalRadialExpansion ha ha1 ((1 + s) • z.val)) = _
  rw [normalRadialExpansion_annulus ha ha1 z hs]



theorem exists_surgeryBall_preserving_radial_germ
    (b : OpenPartialHomeomorph StandardCapSpace A.carrier)
    (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source)
    (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target)
    (hbs : Metric.closedBall 0 1 ⊆ b.source) :
    ∃ (r : ℝ) (D : SurgeryBallEmbedding A),
      0 < r ∧ r < 1 / 2 ∧ D.closedBall = b '' Metric.closedBall 0 1 ∧
      D.map '' Metric.ball 0 2 ⊆ b.target ∧
      ∀ (z : UnitTwoSphere) (s : ℝ), |s| < r →
        D.map ((1 + s) • z.val) = b ((1 + s) • z.val) := by
  obtain ⟨a, B, ha, ha1, hB, hBt, hradial⟩ :=
    exists_surgeryBall_of_ballNeighborhood b hb hbi hbs
  refine ⟨a / 8, normalCorrectedBall ha ha1 B, by positivity, by linarith,
    (normalCorrectedBall_closedBall ha ha1 B).trans hB,
    (normalCorrectedBall_image_subset ha ha1 B).trans hBt, ?_⟩
  intro z s hs
  have hsa : -(1 / 8) < s / a := (lt_div_iff₀ ha).mpr (by
    have h := (abs_lt.mp hs).1
    linarith)
  rw [normalCorrectedBall_annulus ha ha1 B z hs.le,
    hradial z (1 + s / a) (by linarith)]
  congr 2
  field_simp
  ring

end PoincareConjecture.M38
