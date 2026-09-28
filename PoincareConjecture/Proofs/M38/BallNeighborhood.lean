import PoincareConjecture.Proofs.M38.CapBallEmbedding

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38

variable {A : GeneralizedSliceCarrier.{u}}
  (b : OpenPartialHomeomorph StandardCapSpace A.carrier)
  (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source)
  (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target)
  {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
  (hdom : Metric.ball (0 : StandardCapSpace) (1 + a) ⊆ b.source)

noncomputable def ballNeighborhoodSurgeryBall : SurgeryBallEmbedding A := by
  let e := capRadialDiffeomorph 1 a ha ha1
  let f : StandardCapSpace → A.carrier := b ∘ e
  let g : A.carrier → StandardCapSpace := e.symm ∘ b.symm
  have he : MapsTo e (Metric.ball 0 2) b.source := by
    intro x hx
    apply hdom
    rw [← capRadialDiffeomorph_ball_two ha ha1]
    exact mem_image_of_mem e hx
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (Metric.ball 0 2) :=
    hb.comp e.contMDiff.contMDiffOn he
  have htarget : f '' Metric.ball 0 2 ⊆ b.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact b.map_source (he hx)
  have hg : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g (f '' Metric.ball 0 2) :=
    e.symm.contMDiff.comp_contMDiffOn (hbi.mono htarget)
  have hleft : LeftInvOn g f (Metric.ball 0 2) := by
    intro x hx
    change e.symm (b.symm (b (e x))) = x
    rw [b.left_inv (he hx), e.symm_apply_apply]
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

theorem ballNeighborhoodSurgeryBall_closedBall :
    (ballNeighborhoodSurgeryBall b hb hbi ha ha1 hdom).closedBall =
      b '' Metric.closedBall 0 1 := by
  change (b ∘ capRadialDiffeomorph 1 a ha ha1) '' Metric.closedBall 0 1 = _
  rw [image_comp, capRadialDiffeomorph_closedBall ha ha1]

theorem ballNeighborhoodSurgeryBall_image :
    (ballNeighborhoodSurgeryBall b hb hbi ha ha1 hdom).map '' Metric.ball 0 2 =
      b '' Metric.ball 0 (1 + a) := by
  change (b ∘ capRadialDiffeomorph 1 a ha ha1) '' Metric.ball 0 2 = _
  rw [image_comp, capRadialDiffeomorph_ball_two ha ha1]

theorem ballNeighborhoodSurgeryBall_radial (z : UnitTwoSphere) {t : ℝ}
    (ht : 1 / 2 ≤ t) :
    (ballNeighborhoodSurgeryBall b hb hbi ha ha1 hdom).map (t • z.val) =
      b ((1 + a * (t - 1)) • z.val) := by
  change b (capRadialDiffeomorph 1 a ha ha1 (t • z.val)) = _
  rw [capRadialDiffeomorph_smul ha ha1 z t ht]

include hb hbi in

theorem exists_surgeryBall_of_ballNeighborhood
    (hbs : Metric.closedBall 0 1 ⊆ b.source) :
    ∃ (a : ℝ) (B : SurgeryBallEmbedding A),
      0 < a ∧ a < 1 ∧ B.closedBall = b '' Metric.closedBall 0 1 ∧
      B.map '' Metric.ball 0 2 ⊆ b.target ∧
      ∀ (z : UnitTwoSphere) (t : ℝ), 1 / 2 ≤ t →
        B.map (t • z.val) = b ((1 + a * (t - 1)) • z.val) := by
  obtain ⟨a, ha, ha1, hdom⟩ := exists_cap_ball_width zero_lt_one b.open_source hbs
  refine ⟨a, ballNeighborhoodSurgeryBall b hb hbi ha ha1 hdom, ha, ha1,
    ballNeighborhoodSurgeryBall_closedBall b hb hbi ha ha1 hdom, ?_,
    fun z _ ht => ballNeighborhoodSurgeryBall_radial b hb hbi ha ha1 hdom z ht⟩
  rw [ballNeighborhoodSurgeryBall_image]
  rintro _ ⟨x, hx, rfl⟩
  exact b.map_source (hdom hx)

end PoincareConjecture.M38
