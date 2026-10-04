import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.Initial.ParameterBranch
import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.Centered.RealCoefficientSource

/-!
# Actual parameter response from coefficient data

Initial vanishing and uniform local Lipschitz bounds construct the
centered residual needed by the initial-parameter branch. MT2007
Claim 19.1, p. 437; `2026-09-21-coefficient-parameter-response.md`.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareMT.M63

open SpectralHeatNative QuasilinearDeTurckNative

/-- Actual coefficient data gives a positive-time parameter response
and closed H2 trace dependence, with the exact nonlinear forcing
equation. MT2007 Claim 19.1, p. 437; coefficient parameter derivation.
No centered residual or pre-existing solution is assumed. -/
theorem exists_coefficient_parameter_response
    {iota E : Type*} [Countable iota]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
    [MeasurableSpace (State iota)] [BorelSpace (State iota)]
    (lambda : iota → NNReal) (w : State iota) {Tcap r0 : ℝ} {k : ℕ∞}
    (hTcap : 0 < Tcap) (hr0 : 0 < r0) (hk : k ≠ 0)
    (M : E →L[ℝ] State iota →L[ℝ] State iota)
    (G : ℝ × State iota → E) (Q : ℝ × State iota → State iota)
    (hG : ContDiff ℝ k G) (hQ : ContDiff ℝ k Q) (hzero : G (0, w) = 0)
    (hLip : ∀ R : ℝ, 0 ≤ R → ∃ KG KQ : NNReal, ∀ t u v,
      ‖u‖ ≤ R → ‖v‖ ≤ R →
        ‖G (t, u) - G (t, v)‖ ≤ KG * ‖u - v‖ ∧
        ‖Q (t, u) - Q (t, v)‖ ≤ KQ * ‖u - v‖) :
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ Tcap ∧ T ≤ 1 ∧
      ∃ (F : ForcingSpace iota T) (u : State iota → ForcingSpace iota T),
        ‖F‖ < r0 / 2 ∧ u w = F ∧ ContDiffAt ℝ k u w ∧
        ContDiffAt ℝ k (fun w' => initialResponseTrace lambda w' hT.le (u w')) w ∧
        (∀ᶠ w' in 𝓝 w, ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
          u w' t =
            M (G (t, initialResponseTrace lambda w' hT.le (u w') ⟨t, ht⟩))
              (initialHeatHigh lambda w' t + shiftedHighOperator hT.le lambda (u w') t -
                shiftedBaseMultiplier lambda
                  (initialResponseTrace lambda w' hT.le (u w') ⟨t, ht⟩)) +
              Q (t, initialResponseTrace lambda w' hT.le (u w') ⟨t, ht⟩)) ∧
        ∀ t : Icc (0 : ℝ) T,
          ‖initialResponseTrace lambda w hT.le F t - heat lambda (t : ℝ).toNNReal w‖ < r0 := by
  obtain ⟨KG, KQ, hcoeff⟩ := hLip (‖w‖ + r0) (by positivity)
  obtain ⟨T1, hT1, hT1cap, N, _hepsEq, _hprincipal, _hlower, heps, hsource⟩ :=
    exists_centeredRealCoefficientSource lambda w hTcap hr0 M
      (fun t u => G (t, u)) (fun t u => Q (t, u)) hG.continuous hQ.continuous KG KQ
      (fun t _ u v hu hv => (hcoeff t u v hu hv).1)
      (fun t _ u v hu hv => (hcoeff t u v hu hv).2) hzero
  have huncut := hsource.mono (fun _ ht x hx => (ht x).2 hx)
  obtain ⟨T, hT, hTT1, hrest⟩ :=
    N.exists_initial_parameter_branch hT1 hr0 heps hk M G Q hG hQ huncut
  exact ⟨T, hT, hTT1.trans hT1cap, hrest⟩

end PoincareMT.M63
