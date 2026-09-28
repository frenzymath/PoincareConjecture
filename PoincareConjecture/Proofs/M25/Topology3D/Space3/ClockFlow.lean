import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlowAlgebra
import Mathlib.Analysis.Calculus.MeanValue











set_option autoImplicit false

open scoped NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]



def clockField (V : ℝ × E → E) (p : ℝ × E) : ℝ × E := (1, V p)

variable (V : ℝ × E → E) {K L : ℝ≥0}
variable (hK : LipschitzWith K (clockField V)) (hL : ∀ p, ‖clockField V p‖ ≤ L)


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


noncomputable def clockEvolution (s t : ℝ) (x : E) : E :=
  (boundedFlow (clockField V) hK hL (s, x) (t - s)).2


theorem boundedClockFlow_eq (s t : ℝ) (x : E) :
    boundedFlow (clockField V) hK hL (s, x) (t - s) =
      (t, clockEvolution V hK hL s t x) := by
  apply Prod.ext
  · rw [boundedClockFlow_fst]
    change s + (t - s) = t
    ring
  · rfl


@[simp] theorem clockEvolution_self (s : ℝ) (x : E) :
    clockEvolution V hK hL s s x = x := by
  simp only [clockEvolution, sub_self, boundedFlow_zero]


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


theorem clockEvolution_trans (s t u : ℝ) (x : E) :
    clockEvolution V hK hL t u (clockEvolution V hK hL s t x) =
      clockEvolution V hK hL s u x := by
  change (boundedFlow (clockField V) hK hL
    (t, clockEvolution V hK hL s t x) (u - t)).2 = _
  rw [← boundedClockFlow_eq, ← boundedFlow_add]
  have htime : t - s + (u - t) = u - s := by ring
  rw [htime]
  rfl


@[simp] theorem clockEvolution_reverse (s t : ℝ) (x : E) :
    clockEvolution V hK hL t s (clockEvolution V hK hL s t x) = x := by
  rw [clockEvolution_trans, clockEvolution_self]



noncomputable def clockEvolutionEquiv (s t : ℝ) : E ≃ E where
  toFun := clockEvolution V hK hL s t
  invFun := clockEvolution V hK hL t s
  left_inv := clockEvolution_reverse V hK hL s t
  right_inv := clockEvolution_reverse V hK hL t s

end PoincareConjecture.M25.Topology3D
