import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Difference
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Push

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]

theorem exists_cap_graph_normalization
    (P : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞)
    (hball : P '' ball (0 : E) 1 = ball (0 : E) 1)
    {ε : Real} (hε : 0 < ε) (hε1 : ε < 1)
    (hcollar : ∀ x : E, |‖x‖ - 1| < ε → ‖P x‖ = ‖x‖) :
    ∃ K : Set (E × Real), IsCompact K ∧ K ⊆ ball (0 : E) 1 ×ˢ Ioi 0 ∧
      ∃ F : Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, E × Real)
          (E × Real) (E × Real) ∞,
        (∀ p, (F p).1 = p.1) ∧
        (∀ p ∉ K, F p = p) ∧
        ∀ x ∈ ball (0 : E) 1,
          F (x, boundedCapHeight (‖P.symm x‖ ^ 2)) =
            (x, boundedCapHeight (‖x‖ ^ 2)) := by
  obtain ⟨b, hb, hbc, hbsupport, hbin, _⟩ :=
    exists_smooth_cap_height_difference P hball hε hε1 hcollar
  let α : E → Real := fun x => boundedCapHeight (‖P.symm x‖ ^ 2)
  have hinside (x : E) (hx : x ∈ ball (0 : E) 1) : P.symm x ∈ ball (0 : E) 1 := by
    rw [← hball] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have hα : ContinuousOn α (tsupport b) := by
    intro x hx
    exact ((contDiffAt_boundedCapHeight_norm_sq
      (mem_ball_zero_iff.mp (hinside x (hbsupport hx)))).comp x
      P.symm.contMDiff.contDiff.contDiffAt).continuousAt.continuousWithinAt
  have hpos (x : E) (hx : x ∈ ball (0 : E) 1) :
      0 < boundedCapHeight (‖x‖ ^ 2) := by
    have hn := mem_ball_zero_iff.mp hx
    have := one_le_boundedCapHeight (sq_nonneg ‖x‖)
      (show ‖x‖ ^ 2 < 1 by nlinarith [norm_nonneg x])
    linarith
  have hadd (x : E) (hx : x ∈ ball (0 : E) 1) :
      α x + b x = boundedCapHeight (‖x‖ ^ 2) := by
    rw [hbin x hx]
    dsimp [α]
    ring
  obtain ⟨K, hK, hKO, F, hFfirst, hFfix, hFgraph⟩ :=
    exists_supported_transport_between_graphs α b hb hbc hα
      (isOpen_ball.prod isOpen_Ioi) (fun x hx t ht => by
        refine ⟨hbsupport hx, ?_⟩
        change 0 < α x + t * b x
        have h0 : 0 < α x := hpos _ (hinside x (hbsupport hx))
        have h1 : 0 < α x + b x := by rw [hadd x (hbsupport hx)]; exact hpos x (hbsupport hx)
        by_cases hb0 : 0 ≤ b x
        · exact add_pos_of_pos_of_nonneg h0 (mul_nonneg ht.1 hb0)
        · have hmul := mul_le_mul_of_nonpos_right ht.2 (le_of_not_ge hb0)
          nlinarith)
  refine ⟨K, hK, hKO, F, hFfirst, hFfix, ?_⟩
  intro x hx
  simpa only [hadd x hx] using hFgraph x

end Poincare.Manifold.Schoenflies
