import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Restricted Lp pullback under measure-preserving maps

An almost-everywhere image inclusion suffices for restricted norm
control and representative transport. Source: the translation step
of M64's inward-boundary-approximation derivation.

Morgan--Tian context: Lemma 19.15, printed pp. 447-449. This project analytic helper
supports the actual annular minimizer and boundary regularity construction.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter MeasureTheory
open scoped ENNReal

namespace PoincareMT

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] {mu : Measure X} {nu : Measure Y}
  {T : X → Y} {K : Set X} {O : Set Y} {p : ℝ≥0∞}

/-- Restricted Lp values and their norm are controlled by the original domain whenever the
image lies there almost everywhere. This permits the null physical face in M64's inward
approximation. Source: derivations/2026-09-26-inward-boundary-approximation.md, translation
and extension. -/
theorem m64MeasurePreserving_memLp_restrict
    (hT : MeasurePreserving T mu nu) (hO : MeasurableSet O)
    (hbase : ∀ᵐ x ∂mu.restrict K, T x ∈ O)
    {u : Y → E} (hu : MemLp u p (nu.restrict O)) :
    MemLp (u ∘ T) p (mu.restrict K) ∧
      eLpNorm (u ∘ T) p (mu.restrict K) ≤ eLpNorm u p (nu.restrict O) := by
  classical
  let U := O.indicator u
  have hU : MemLp U p nu := (memLp_indicator_iff_restrict hO).mpr hu
  have heq : U ∘ T =ᵐ[mu.restrict K] u ∘ T := by
    filter_upwards [hbase] with x hx
    exact indicator_of_mem hx u
  refine ⟨((hU.comp_measurePreserving hT).restrict K).ae_eq heq, ?_⟩
  calc
    _ = eLpNorm (U ∘ T) p (mu.restrict K) := eLpNorm_congr_ae heq.symm
    _ ≤ eLpNorm (U ∘ T) p mu := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = eLpNorm U p nu := eLpNorm_comp_measurePreserving hU.aestronglyMeasurable hT
    _ = _ := eLpNorm_indicator_eq_eLpNorm_restrict hO

/-- Actual almost-everywhere data on the original domain pull back to a restricted set with
almost-everywhere image inclusion. Source: M64's inward approximation derivation, transport
of the original columns. Source/construction:
proof-work/tasks/M64/derivations/2026-09-26-inward-boundary-approximation.md, Translation
and extension. -/
theorem m64MeasurePreserving_ae_restrict
    (hT : MeasurePreserving T mu nu) (hO : MeasurableSet O)
    (hbase : ∀ᵐ x ∂mu.restrict K, T x ∈ O)
    {P : Y → Prop} (hP : ∀ᵐ y ∂nu.restrict O, P y) :
    ∀ᵐ x ∂mu.restrict K, P (T x) := by
  have hall := hT.quasiMeasurePreserving.ae ((ae_restrict_iff' hO).mp hP)
  filter_upwards [ae_restrict_of_ae hall, hbase] with x hx hb
  exact hx hb

end PoincareMT
