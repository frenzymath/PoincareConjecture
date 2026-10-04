import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Real

/-!
# Removing boundary spheres from finite-dimensional Haar integrals

Morgan-Tian Definition 18.17, printed p. 430. Boundary circles do not
contribute to disk or annular area. The following measure identity
applies in every nonzero finite dimension and for every real radius.
-/

set_option autoImplicit false

open Set Metric MeasureTheory Filter

namespace PoincareMT.M60

/-- Open and closed balls agree almost everywhere for a Haar measure
in a nonzero finite-dimensional real normed space. Source: MT
Definition 18.17, p. 430, null-boundary step for collar areas. -/
theorem haar_ball_ae_eq_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (x : E) (r : ℝ) : ball x r =ᵐ[μ] closedBall x r := by
  filter_upwards [compl_mem_ae_iff.mpr (Measure.addHaar_sphere μ x r)] with y hy
  have hne : dist y x ≠ r := hy
  exact propext ⟨le_of_lt, fun h => lt_of_le_of_ne h hne⟩

/-- The volume of a unit annulus follows directly from Haar scaling.
This formula also covers dimension zero. Source: MT Definition 18.17,
p. 430, quantitative collar-area bound. -/
theorem haar_unit_annulus_real {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    μ.real ((closedBall (0 : E) r)ᶜ ∩ closedBall 0 1) =
      (1 - r ^ Module.finrank ℝ E) * μ.real (closedBall (0 : E) 1) := by
  let : ProperSpace E := FiniteDimensional.proper ℝ E
  have hset : (closedBall (0 : E) r)ᶜ ∩ closedBall 0 1 =
      closedBall 0 1 \ closedBall 0 r := inter_comm _ _
  rw [hset, measureReal_sdiff (closedBall_subset_closedBall hr1) measurableSet_closedBall
      (isCompact_closedBall (0 : E) 1).measure_ne_top,
    Measure.addHaar_real_closedBall' μ (0 : E) hr]
  ring

end PoincareMT.M60
