import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Model.CapBody
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Model.CollarGeometry
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Model.CapComplement







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Reverse
open _root_.PoincareConjecture

namespace M38Schoenflies











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Reverse

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1

open Poincare.Geometry.Euclidean



theorem exists_asymmetric_cap_lens
    {v : E3} (hv : ‖v‖ = 1) (b s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (γ : S1 → Hemisphere.Plane v)
    (hboundary : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (g : E2 → E3) (hgi : Injective g)
    (hcore : g '' closedBall (0 : E2) 1 =
      liftPlaneDiffeomorph hv b s hs A '' boundedCylinderNorthernCap v)
    {η r : Real} (hr : 1 < r) (hr' : r ≤ 5 / 4) (hrη : r - 1 < η)
    (hcollar : ∀ q : S1, ∀ ρ : Real, |ρ - 1| < η →
      g (ρ • (q : E2)) = (b + s * capCollarClock ρ) • v + (γ q : E3)) :
    ∃ (d : Real) (hd : d ≠ 0) (L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
      d = s * capCollarClock r ∧ s * d < 0 ∧ |d| < |s| ∧
      L '' sphere (0 : E3) 1 =
        (liftPlaneDiffeomorph hv b d hd A '' boundedCylinderNorthernCap v) ∪
          (g '' closedBall (0 : E2) 1) ∧
      g '' closedBall (0 : E2) r ⊆ L '' sphere (0 : E3) 1 ∧
      (∀ y ∈ (L '' sphere (0 : E3) 1) \ (g '' closedBall (0 : E2) r),
        (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' ball 0 1) ∧
      (∀ y ∈ L '' closedBall (0 : E3) 1,
        (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1 ∧
        |inner Real v y - b| ≤ 2 * |s|) ∧
      (L '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1) =
        liftPlaneDiffeomorph hv b d hd A '' boundedCylinderNorthernCap v := by
  let d := s * capCollarClock r
  have hclock := capCollarClock_neg_of_one_lt hr
  have hd : d ≠ 0 := mul_ne_zero hs hclock.ne
  have hopposite : s * d < 0 := by
    change s * (s * capCollarClock r) < 0
    rw [← mul_assoc]
    exact mul_neg_of_pos_of_neg (mul_self_pos.mpr hs) hclock
  have hdabs : |d| < |s| := by
    have hb := (capCollarClock_bounds hr.le hr').1
    have hcabs : |capCollarClock r| ≤ 1 / 4 := by
      rw [abs_of_neg hclock]
      linarith
    dsimp [d]
    rw [abs_mul]
    nlinarith [abs_pos.mpr hs, abs_nonneg s]
  obtain ⟨L, hL⟩ := exists_ambient_two_caps_of_opposite_scales hv b s d hs hd hopposite A
  rw [← hcore] at hL
  refine ⟨d, hd, L, rfl, hopposite, hdabs, hL, ?_, ?_, ?_, ?_⟩
  · rw [hL]
    exact extended_cap_subset_opposite_union_core hv b s d hs hd A γ hboundary g
      hr hrη rfl hcollar
  · rintro y ⟨hy, hn⟩
    rw [hL] at hy
    rcases hy with hy | hy
    · obtain ⟨q, hq, heq⟩ := (transported_cap_bounds hv b d hd A hy).2.1
      refine ⟨q, mem_ball_zero_iff.mpr ?_, heq⟩
      have hle := mem_closedBall_zero_iff.mp hq
      apply lt_of_le_of_ne hle
      intro hnq
      apply hn
      exact opposite_cap_circle_point_mem_extended hv b s d hs hd A γ hboundary g
        hr hrη rfl hcollar hy ⟨q, mem_sphere_zero_iff_norm.mpr hnq, heq⟩
    · exact False.elim (hn (image_mono (closedBall_subset_closedBall hr.le) hy))
  · apply filled_ball_cylinder_bounds hv b (2 * |s|) (by positivity) A L
    intro y hy
    rw [hL] at hy
    rcases hy with hy | hy
    · have hb := (transported_cap_bounds hv b d hd A hy).2
      exact ⟨hb.1, hb.2.trans (by linarith [hdabs])⟩
    · exact (transported_cap_bounds hv b s hs A (hcore ▸ hy)).2
  · rw [hL]
    exact opposite_cap_union_diff_open_cap hv b s d hs hd hopposite A γ hboundary g hgi
      hcore (by linarith) hcollar

end Poincare.Manifold.Schoenflies.Reverse

end

end M38Schoenflies
