import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Step.OtherLevels

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryStep

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 -> E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)

private theorem retained_eventuallyEq
    (g : S2 -> E3) (e : OpenPartialHomeomorph E2 S2)
    (hes : closedBall 0 1 ⊆ e.source)
    (heq : ∀ q ∈ e '' closedBall 0 1, g q = S.D (f q))
    {p : S2} (hp : p ∈ e '' ball 0 1) (hfar : R < |inner Real v (f p) - c|) :
    g =ᶠ[𝓝 p] f := by
  have hopen := e.isOpen_image_of_subset_source isOpen_ball
    (ball_subset_closedBall.trans hes)
  have hcont : Continuous (fun q => |inner Real v (f q) - c|) :=
    (((innerSL Real v).continuous.comp S.original_embedding.contMDiff.continuous).sub
      continuous_const).abs
  filter_upwards [hopen.mem_nhds hp, (isOpen_lt continuous_const hcont).mem_nhds hfar]
    with q hq hqfar
  rw [heq q (image_mono ball_subset_closedBall hq)]
  apply S.eq_self_off
  intro hK
  exact (not_le_of_gt hqfar) (S.support_subset hK)

theorem protected_point_survives {p : S2} (hfar : R < |inner Real v (f p) - c|) :
    (p ∈ S.eMinus '' ball 0 1 ∧ S.fMinus =ᶠ[𝓝 p] f) ∨
      (p ∈ S.ePlus '' ball 0 1 ∧ S.fPlus =ᶠ[𝓝 p] f) := by
  have hnot : p ∉ S.T '' (univ ×ˢ Icc (-S.a) S.a) := by
    rintro ⟨⟨q, t⟩, ⟨_, ht⟩, hqp⟩
    have htε : t ∈ Ioo (-S.ε) S.ε := by
      constructor <;> linarith [S.a_lt_quarter_ε, S.ε_pos, ht.1, ht.2]
    have hheight := S.tube_height q t htε
    rw [hqp] at hheight
    have htbound : |t| ≤ S.a := abs_le.mpr ht
    rw [hheight, add_sub_cancel_left] at hfar
    linarith [S.a_lt_quarter_R, S.a_pos]
  rw [S.slab_eq, mem_compl_iff, not_not] at hnot
  rcases hnot with hM | hP
  · exact Or.inl ⟨hM, S.retained_eventuallyEq S.fMinus S.eMinus S.eMinus_source
      S.retainedMinus_eq hM hfar⟩
  · exact Or.inr ⟨hP, S.retained_eventuallyEq S.fPlus S.ePlus S.ePlus_source
      S.retainedPlus_eq hP hfar⟩

theorem protected_minus_eventuallyEq {p : S2}
    (hfar : R < |inner Real v (S.fMinus p) - c|) : S.fMinus =ᶠ[𝓝 p] f := by
  have hp : p ∈ S.eMinus '' ball 0 1 := by
    by_contra hnot
    have hd : p ∈ S.dMinus '' closedBall 0 1 := by rw [S.dMinus_closed]; exact hnot
    obtain ⟨x, hx, rfl⟩ := hd
    rw [S.capMinus_eq x hx] at hfar
    exact (not_lt_of_ge hfar.le) (S.capMinus_height_mem_slab x)
  have heq := S.retainedMinus_eq p (image_mono ball_subset_closedBall hp)
  have hheight : inner Real v (S.fMinus p) = inner Real v (f p) := by
    rw [heq, S.height_preserving]
  exact S.retained_eventuallyEq S.fMinus S.eMinus S.eMinus_source
    S.retainedMinus_eq hp (hheight ▸ hfar)

theorem protected_plus_eventuallyEq {p : S2}
    (hfar : R < |inner Real v (S.fPlus p) - c|) : S.fPlus =ᶠ[𝓝 p] f := by
  have hp : p ∈ S.ePlus '' ball 0 1 := by
    by_contra hnot
    have hd : p ∈ S.dPlus '' closedBall 0 1 := by rw [S.dPlus_closed]; exact hnot
    obtain ⟨x, hx, rfl⟩ := hd
    rw [S.capPlus_eq x hx] at hfar
    exact (not_lt_of_ge hfar.le) (S.capPlus_height_mem_slab x)
  have heq := S.retainedPlus_eq p (image_mono ball_subset_closedBall hp)
  have hheight : inner Real v (S.fPlus p) = inner Real v (f p) := by
    rw [heq, S.height_preserving]
  exact S.retained_eventuallyEq S.fPlus S.ePlus S.ePlus_source
    S.retainedPlus_eq hp (hheight ▸ hfar)

end Poincare.Manifold.Schoenflies.SphereSurgeryStep

end

end M38Schoenflies
