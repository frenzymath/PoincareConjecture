import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Cap.StandardScalar
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The barrier constants in Proposition 16.13

The top-entry scalar integral diverges as the normalized top time tends
to one. The side-entry energy lower bound is quadratic in the outer cap
radius. These elementary choices precede the Proposition 16.5 cutoff.

Source: Morgan--Tian Proposition 16.13 and its proof, pp. 376-378.
The strict inequalities also cover nonpositive requested action bounds.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.Proofs.M46

/-- Choose the normalized top time in Proposition 16.13, p. 377, by
solving the logarithmic lower bound explicitly. The scalar coefficient
`c` is positive and fixed before the requested action bound `ell`. -/
theorem exists_capTopBarrierTime (c : ℝ) (hc : 0 < c) (ell : ℝ) :
    ∃ theta : ℝ, 1 / 2 < theta ∧ theta < 1 ∧
      ell < -(c / 2) * (Real.log (1 - theta) + Real.log 2) := by
  let q : ℝ := 2 * (max ell 0 + 1) / c
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  have hexp : 0 < Real.exp (-q) := Real.exp_pos _
  have hexpOne : Real.exp (-q) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hq)
  let theta : ℝ := 1 - Real.exp (-q) / 2
  have htheta : 1 / 2 < theta := by dsimp only [theta]; linarith
  have hthetaOne : theta < 1 := by dsimp only [theta]; linarith
  have hlog : Real.log (1 - theta) + Real.log 2 = -q := by
    have hsub : 1 - theta = Real.exp (-q) / 2 := by dsimp only [theta]; ring
    rw [hsub, Real.log_div hexp.ne' (by norm_num), Real.log_exp]
    ring
  refine ⟨theta, htheta, hthetaOne, ?_⟩
  rw [hlog]
  have heq : -(c / 2) * -q = max ell 0 + 1 := by
    dsimp only [q]
    field_simp [hc.ne']
  rw [heq]
  exact lt_of_le_of_lt (le_max_left ell 0) (lt_add_one _)

/-- Choose the outer radius after the top time, retaining any independently
required radius threshold. This strengthens the numerical choice in
Proposition 16.13, p. 378, enough to make the action bound strict even
when `ell` is nonpositive. -/
theorem exists_capSideBarrierRadius (ell lowerRadius : ℝ) :
    ∃ A0 : ℝ, 0 < A0 ∧ lowerRadius ≤ A0 ∧
      ∀ A : ℝ, A0 ≤ A → ell < A ^ 2 / 75 := by
  let q : ℝ := max ell 0 + 1
  have hq : 0 < q := by dsimp only [q]; positivity
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  refine ⟨max lowerRadius (10 * Real.sqrt q),
    (by exact lt_of_lt_of_le (by positivity) (le_max_right _ _)),
    le_max_left _ _, ?_⟩
  intro A hA
  have hlarge : 10 * Real.sqrt q ≤ A := (le_max_right _ _).trans hA
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  have hell : ell < q := by
    exact lt_of_le_of_lt (le_max_left ell 0) (lt_add_one _)
  have hnonneg : 0 ≤ A := (by positivity : 0 ≤ 10 * Real.sqrt q).trans hlarge
  have hbound : 100 * q ≤ A ^ 2 := by nlinarith
  nlinarith

/-- The stored M35 scalar rate fixes `c` before the action threshold;
then Proposition 16.13, p. 377, chooses its normalized top time. -/
theorem exists_standardCapTopBarrier {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) :
    ∃ c : ℝ, 0 < c ∧
      (∀ t ∈ Set.Ico 0 P.standard_cap.flow.base.lifetime,
        ∀ x : StandardCapSpace,
          c / (1 - t) ≤ (P.standard_cap.flow.connection t).scalarCurvature x) ∧
      ∀ ell : ℝ, ∃ theta : ℝ, 1 / 2 < theta ∧ theta < 1 ∧
        ell < -(c / 2) * (Real.log (1 - theta) + Real.log 2) := by
  obtain ⟨c, hc, hscalar⟩ := P.standardScalarRate
  exact ⟨c, hc, hscalar, exists_capTopBarrierTime c hc⟩

end PoincareMT.Proofs.M46
