import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.CapCollar







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



set_option autoImplicit false

open Set Metric Function
open _root_.Poincare.Manifold.Schoenflies.Reverse
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

namespace Reverse

theorem image_ball_eq_diff_sphere (g : E2 → E3) (hgi : Injective g) :
    g '' ball (0 : E2) 1 = (g '' closedBall 0 1) \ (g '' sphere 0 1) := by
  rw [← image_sdiff hgi]
  congr 1
  ext x
  simp only [mem_ball_zero_iff, mem_sdiff, mem_closedBall_zero_iff,
    mem_sphere_zero_iff_norm]
  exact lt_iff_le_and_ne

theorem image_circle_of_cap_collar
    (g : E2 → E3) {v : E3} (γ : S1 → Hemisphere.Plane v) (b s : Real)
    {η : Real} (hη : 0 < η)
    (hcollar : ∀ q : S1, ∀ ρ : Real, |ρ - 1| < η →
      g (ρ • (q : E2)) = (b + s * capCollarClock ρ) • v + (γ q : E3)) :
    g '' sphere (0 : E2) 1 = range (fun q : S1 => b • v + (γ q : E3)) := by
  have hq (q : S1) : g q = b • v + (γ q : E3) := by
    simpa only [one_smul, capCollarClock_one, mul_zero, add_zero] using
      hcollar q 1 (by simpa using hη)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, (hq ⟨x, hx⟩).symm⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q, q.property, hq q⟩

end Reverse

namespace SphereSurgeryStep

variable {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)

theorem open_capMinus_range_of_collar
    (g : E2 → E3) (hgi : Injective g)
    (hcore : g '' closedBall (0 : E2) 1 = S.gMinus '' closedBall 0 1)
    {η : Real} (hη : 0 < η)
    (hcollar : ∀ q : S1, ∀ ρ : Real, |ρ - 1| < η →
      g (ρ • (q : E2)) =
        (c - S.a + S.s * Reverse.capCollarClock ρ) • v + (S.γ q : E3)) :
    g '' ball (0 : E2) 1 = S.gMinus '' ball (0 : E2) 1 := by
  rw [Reverse.image_ball_eq_diff_sphere g hgi,
    Reverse.image_ball_eq_diff_sphere S.gMinus S.gMinus_injective, hcore,
    S.capMinus_edge_eq_cutting_circle,
    Reverse.image_circle_of_cap_collar g S.γ (c - S.a) S.s hη hcollar]

theorem open_capPlus_range_of_collar
    (g : E2 → E3) (hgi : Injective g)
    (hcore : g '' closedBall (0 : E2) 1 = S.gPlus '' closedBall 0 1)
    {η : Real} (hη : 0 < η)
    (hcollar : ∀ q : S1, ∀ ρ : Real, |ρ - 1| < η →
      g (ρ • (q : E2)) =
        (c + S.a + (-S.s) * Reverse.capCollarClock ρ) • v + (S.γ q : E3)) :
    g '' ball (0 : E2) 1 = S.gPlus '' ball (0 : E2) 1 := by
  rw [Reverse.image_ball_eq_diff_sphere g hgi,
    Reverse.image_ball_eq_diff_sphere S.gPlus S.gPlus_injective, hcore,
    S.capPlus_edge_eq_cutting_circle,
    Reverse.image_circle_of_cap_collar g S.γ (c + S.a) (-S.s) hη hcollar]

end SphereSurgeryStep

end Poincare.Manifold.Schoenflies

end M38Schoenflies
