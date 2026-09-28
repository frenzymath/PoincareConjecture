import PoincareConjecture.Proofs.M38.BallCoverDescent
import PoincareConjecture.Proofs.M38.InnermostBallTranslates











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38



theorem exists_surgeryBall_descend_with_frontier
    {A Q : GeneralizedSliceCarrier.{u}} (q : A.carrier → Q.carrier)
    (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    {I : Type*} [Finite I] (f : I → A.carrier → A.carrier)
    (hf : ∀ i, Continuous (f i))
    (hfibers : ∀ x y, q x = q y → x = y ∨ ∃ i, y = f i x)
    (B : SurgeryBallEmbedding A)
    (hdisjoint : ∀ i, Disjoint B.closedBall (f i '' B.closedBall)) :
    ∃ D : SurgeryBallEmbedding Q,
      D.closedBall = q '' B.closedBall ∧
      frontier D.closedBall = q '' frontier B.closedBall := by
  obtain ⟨C, hCB, _, hsep⟩ :=
    exists_surgeryBall_with_disjoint_finite_images B f hf hdisjoint
  have hlocal : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞
      (q ∘ C.map) (Metric.ball 0 2) := by
    intro x
    exact (surgeryBall_map_localDiffeomorph A C x.property).comp (𝓡 3) Q.carrier
      (hq (C.map x.val))
  have hinj : InjOn (q ∘ C.map) (Metric.ball 0 2) := by
    intro x hx y hy hxy
    rcases hfibers (C.map x) (C.map y) hxy with heq | ⟨i, hi⟩
    · exact C.left_inverse.injOn hx hy heq
    · exact (disjoint_left.mp (hsep i) (mem_image_of_mem C.map hy)
        ⟨C.map x, mem_image_of_mem C.map hx, hi.symm⟩).elim
  let D := surgeryBallOfLocalDiffeomorph (q ∘ C.map) hlocal hinj
  refine ⟨D, ?_, ?_⟩
  · change (q ∘ C.map) '' Metric.closedBall 0 1 = q '' B.closedBall
    rw [image_comp]
    exact congrArg (q '' ·) hCB
  · rw [surgeryBall_closedBall_frontier D, ← hCB, surgeryBall_closedBall_frontier C]
    change (q ∘ C.map) '' Metric.sphere 0 1 = q '' (C.map '' Metric.sphere 0 1)
    exact image_comp _ _ _




theorem exists_descended_innermost_sphereBall
    {Q : GeneralizedSliceCarrier.{u}}
    {G I : Type*} [Group G] [Finite G] [Finite I] [Nonempty I] [MulAction G I]
    (q : sphereCarrier.{u}.carrier → Q.carrier)
    (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    (e : G → Diffeomorph (𝓡 3) (𝓡 3)
      sphereCarrier.{u}.carrier sphereCarrier.{u}.carrier ∞)
    (heone : ∀ x, e 1 x = x)
    (heinv : ∀ g, (e g).symm = e g⁻¹)
    (hfibers : ∀ x y, q x = q y → ∃ g : G, y = e g x)
    (hfree : ∀ (g : G) (i : I), g • i = i → g = 1)
    (B : I → SurgeryBallEmbedding sphereCarrier.{u})
    (hboundary : ∀ (g : G) (i : I),
      frontier (B (g • i)).closedBall = e g '' frontier (B i).closedBall)
    (hdisjoint : ∀ i j, i ≠ j →
      Disjoint (frontier (B i).closedBall) (frontier (B j).closedBall))
    (p : sphereCarrier.{u}.carrier) (hp : ∀ i, p ∉ (B i).closedBall) :
    ∃ (i : I) (D : SurgeryBallEmbedding Q),
      D.closedBall = q '' (B i).closedBall ∧
      frontier D.closedBall = q '' frontier (B i).closedBall := by
  obtain ⟨i, hi⟩ := exists_innermost_sphereBall B hdisjoint p hp
  have havoid (g : G) (hg : g ≠ 1) :
      Disjoint (B i).closedBall (e g '' frontier (B i).closedBall) := by
    rw [← hboundary]
    exact hi (g • i) (fun h => hg (hfree g i h))
  have hsep (g : G) (hg : g ≠ 1) :
      Disjoint (B i).closedBall (e g '' (B i).closedBall) := by
    apply sphereBall_disjoint_translate_of_innermost (B i) (e g) (havoid g hg)
    rw [heinv]
    exact havoid g⁻¹ (by simpa using hg)
  let f : {g : G // g ≠ 1} → sphereCarrier.{u}.carrier → sphereCarrier.{u}.carrier :=
    fun g => e g.val
  have hfibers' (x y) (hxy : q x = q y) : x = y ∨ ∃ g, y = f g x := by
    obtain ⟨g, hg⟩ := hfibers x y hxy
    by_cases hg1 : g = 1
    · left
      simpa only [hg1, heone] using hg.symm
    · exact Or.inr ⟨⟨g, hg1⟩, hg⟩
  obtain ⟨D, hD, hDf⟩ := exists_surgeryBall_descend_with_frontier q hq f
    (fun g => (e g.val).contMDiff.continuous) hfibers' (B i)
    (fun g => hsep g.val g.property)
  exact ⟨i, D, hD, hDf⟩

end PoincareConjecture.M38
