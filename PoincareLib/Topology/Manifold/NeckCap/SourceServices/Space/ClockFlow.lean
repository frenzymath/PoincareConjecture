import PoincareLib.Topology.Manifold.NeckCap.SourceServices.Space.FlowAlgebra
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Evolution of a time-dependent field using a clock coordinate

An autonomous field `(1, V)` advances its first coordinate at unit speed.
The second coordinate therefore solves the time-dependent equation for
`V`. The autonomous flow law supplies the evolution composition law and
reverse-time inverse. These are the algebraic identities for Hatcher's
ambient isotopies, Notes on Basic 3-Manifold Topology, Lemma 1.2, pp. 2-3.
-/

set_option autoImplicit false

open scoped NNReal

namespace PoincareMT.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The autonomous clock lift of a time-dependent field, used in
Hatcher's restricted isotopy-extension construction, Lemma 1.2. -/
def clockField (V : ℝ × E → E) (p : ℝ × E) : ℝ × E := (1, V p)

variable (V : ℝ × E → E) {K L : ℝ≥0}
variable (hK : LipschitzWith K (clockField V)) (hL : ∀ p, ‖clockField V p‖ ≤ L)

/-- The added clock advances by exactly elapsed time. -/
theorem boundedClockFlow_fst (p : ℝ × E) (t : ℝ) :
    (boundedFlow (clockField V) hK hL p t).1 = p.1 + t := by
  have hd (u : ℝ) : HasDerivAt
      (fun r => (boundedFlow (clockField V) hK hL p r).1) 1 u := by
    simpa only [Function.comp_def, clockField, ContinuousLinearMap.coe_fst'] using
      (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp_hasDerivAt u
        (boundedFlow_hasDerivAt (clockField V) hK hL p u)
  have hz (u : ℝ) : HasDerivAt
      (fun r => (boundedFlow (clockField V) hK hL p r).1 - r) 0 u := by
    convert! (hd u).sub (hasDerivAt_id u) using 1
    simp only [sub_self]
  have hconst := is_const_of_deriv_eq_zero (fun u => (hz u).differentiableAt)
    (fun u => (hz u).deriv) t 0
  simp only [boundedFlow_zero, sub_zero] at hconst
  linarith

/-- Evolution from initial time `s` to final time `t` for the field `V`. -/
noncomputable def clockEvolution (s t : ℝ) (x : E) : E :=
  (boundedFlow (clockField V) hK hL (s, x) (t - s)).2

/-- The full lifted flow records final time and the evolved point. -/
theorem boundedClockFlow_eq (s t : ℝ) (x : E) :
    boundedFlow (clockField V) hK hL (s, x) (t - s) =
      (t, clockEvolution V hK hL s t x) := by
  apply Prod.ext
  · rw [boundedClockFlow_fst]
    change s + (t - s) = t
    ring
  · rfl

/-- Evolution over a zero time interval fixes the initial point. -/
@[simp] theorem clockEvolution_self (s : ℝ) (x : E) :
    clockEvolution V hK hL s s x = x := by
  simp only [clockEvolution, sub_self, boundedFlow_zero]

/-- The evolved point satisfies the original time-dependent equation. -/
theorem clockEvolution_hasDerivAt (s t : ℝ) (x : E) :
    HasDerivAt (fun r => clockEvolution V hK hL s r x)
      (V (t, clockEvolution V hK hL s t x)) t := by
  have hd := (boundedFlow_hasDerivAt (clockField V) hK hL (s, x) (t - s)).scomp t
    ((hasDerivAt_id t).sub_const s)
  have hproj := (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp_hasDerivAt t hd
  have hproj' : HasDerivAt (fun r => clockEvolution V hK hL s r x)
      (V (boundedFlow (clockField V) hK hL (s, x) (t - s))) t := by
    simpa only [Function.comp_def, id_eq, one_smul, clockField, clockEvolution,
      ContinuousLinearMap.coe_snd'] using hproj
  rw [boundedClockFlow_eq] at hproj'
  exact hproj'

/-- Evolution through an intermediate time agrees with direct evolution. -/
theorem clockEvolution_trans (s t u : ℝ) (x : E) :
    clockEvolution V hK hL t u (clockEvolution V hK hL s t x) =
      clockEvolution V hK hL s u x := by
  change (boundedFlow (clockField V) hK hL
    (t, clockEvolution V hK hL s t x) (u - t)).2 = _
  rw [← boundedClockFlow_eq, ← boundedFlow_add]
  have htime : t - s + (u - t) = u - s := by ring
  rw [htime]
  rfl

/-- Returning to the initial time reverses the evolution. -/
@[simp] theorem clockEvolution_reverse (s t : ℝ) (x : E) :
    clockEvolution V hK hL t s (clockEvolution V hK hL s t x) = x := by
  rw [clockEvolution_trans, clockEvolution_self]

/-- Each evolution map has the reverse-time evolution as its inverse.
Smoothness is supplied separately from joint regularity of the lifted flow. -/
noncomputable def clockEvolutionEquiv (s t : ℝ) : E ≃ E where
  toFun := clockEvolution V hK hL s t
  invFun := clockEvolution V hK hL t s
  left_inv := clockEvolution_reverse V hK hL s t
  right_inv := clockEvolution_reverse V hK hL t s

end PoincareMT.M25.Topology3D
