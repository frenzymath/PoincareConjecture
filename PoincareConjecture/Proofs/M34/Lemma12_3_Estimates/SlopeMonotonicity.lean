import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.AxisCurvature
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M34

theorem initialWeightedSlope_deriv_nonpos (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 < r) : deriv (initialWeightedSlope g₀) r ≤ 0 := by
  have h := g₀.nonnegative_sectional (EuclideanSpace.single (0 : Fin 3) r)
    (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
    (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
  rw [initialCurvatureTensor_radial_axis g₀ hr] at h
  have hp : 0 < initialRadialSpeed g₀ r * initialWarping g₀ r / r ^ 2 :=
    div_pos (mul_pos (initialRadialSpeed_pos g₀ r) (initialWarping_pos g₀ hr))
      (sq_pos_of_pos hr)
  nlinarith

theorem initialWeightedSlope_antitoneOn (g₀ : StandardInitialMetric) :
    AntitoneOn (initialWeightedSlope g₀) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (initialWeightedSlope_contDiff g₀).continuous.continuousOn
    ((initialWeightedSlope_contDiff g₀).differentiable (by simp)).differentiableOn
  intro r hr
  exact initialWeightedSlope_deriv_nonpos g₀ (by simpa using hr)

theorem initialRadialLength_strictMono (g₀ : StandardInitialMetric) :
    StrictMono (initialRadialLength g₀) := by
  apply strictMono_of_deriv_pos
  intro r
  rw [(initialRadialLength_hasDerivAt g₀ r).deriv]
  exact initialRadialSpeed_pos g₀ r

theorem initialWeightedSlope_nonneg (g₀ : StandardInitialMetric)
    {r₀ : ℝ} (hr₀ : 0 < r₀) : 0 ≤ initialWeightedSlope g₀ r₀ := by
  by_contra h
  have hq : initialWeightedSlope g₀ r₀ < 0 := lt_of_not_ge h
  have hf₀ := initialWarping_pos g₀ hr₀
  obtain ⟨r, _, hlarge⟩ := initialRadialLength_unbounded g₀
    (initialRadialLength g₀ r₀ + (initialWarping g₀ r₀ + 1) /
      (-initialWeightedSlope g₀ r₀))
  have hlength : initialRadialLength g₀ r₀ < initialRadialLength g₀ r := by
    have hp : 0 < (initialWarping g₀ r₀ + 1) / (-initialWeightedSlope g₀ r₀) :=
      div_pos (by linarith) (neg_pos.mpr hq)
    linarith
  have hrr : r₀ < r := (initialRadialLength_strictMono g₀).lt_iff_lt.mp hlength
  have hd (t : ℝ) : HasDerivAt
      (fun s => initialWarping g₀ s - initialWeightedSlope g₀ r₀ * initialRadialLength g₀ s)
      (deriv (initialWarping g₀) t - initialWeightedSlope g₀ r₀ * initialRadialSpeed g₀ t) t :=
    ((((initialWarping_contDiff g₀).differentiable (by simp)) t).hasDerivAt).sub
      ((initialRadialLength_hasDerivAt g₀ t).const_mul (initialWeightedSlope g₀ r₀))
  have hm : AntitoneOn
      (fun s => initialWarping g₀ s - initialWeightedSlope g₀ r₀ * initialRadialLength g₀ s)
      (Ici r₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici r₀)
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
    intro t ht
    have hrt : r₀ < t := by simpa using ht
    have hle := initialWeightedSlope_antitoneOn g₀ hr₀ (hr₀.trans hrt) hrt.le
    have ha := initialRadialSpeed_pos g₀ t
    change deriv (initialWarping g₀) t / initialRadialSpeed g₀ t ≤
      initialWeightedSlope g₀ r₀ at hle
    rw [(hd t).deriv]
    exact sub_nonpos.mpr ((div_le_iff₀ ha).mp hle)
  have hfall := hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr hrr.le) hrr.le
  have hproduct : initialWarping g₀ r₀ + 1 <
      (initialRadialLength g₀ r - initialRadialLength g₀ r₀) *
        (-initialWeightedSlope g₀ r₀) := by
    apply (div_lt_iff₀ (neg_pos.mpr hq)).mp
    linarith
  have hf := initialWarping_pos g₀ (hr₀.trans hrr)
  dsimp only at hfall
  nlinarith

end PoincareConjecture.M34
