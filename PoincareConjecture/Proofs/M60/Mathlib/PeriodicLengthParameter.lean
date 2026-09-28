import PoincareConjecture.Proofs.M60.Mathlib.CurveLengthParameter
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Convex.Topology

set_option autoImplicit false

open Set
open scoped NNReal

namespace PoincareConjecture.M60

theorem variationOnFromTo_add_period {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ → E} {T : ℝ} (hp : Function.Periodic f T) (a b : ℝ) :
    variationOnFromTo f univ (a + T) (b + T) = variationOnFromTo f univ a b := by
  let tau := fun t : ℝ => t + T
  have himage : tau '' univ = univ :=
    image_univ_of_surjective (fun y => ⟨y - T, sub_add_cancel y T⟩)
  have hcomp : f ∘ tau = f := funext hp
  have h := variationOnFromTo.comp_eq_of_monotoneOn f tau
    ((monotone_id.add_const T).monotoneOn univ) (mem_univ a) (mem_univ b)
  rw [himage, hcomp] at h
  exact h.symm

theorem lengthParameter_add_period {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ → E} {T : ℝ} (hf : LocallyBoundedVariationOn f univ)
    (hp : Function.Periodic f T) (t : ℝ) :
    variationOnFromTo f univ 0 (t + T) =
      variationOnFromTo f univ 0 t + variationOnFromTo f univ 0 T := by
  have h := variationOnFromTo.add hf (mem_univ 0) (mem_univ T) (mem_univ (t + T))
  have hshift := variationOnFromTo_add_period hp 0 t
  rw [zero_add] at hshift
  rw [hshift] at h
  exact h.symm.trans (add_comm _ _)

theorem naturalParameterization_add_periodLength {E : Type*} [EMetricSpace E]
    {f : ℝ → E} {T : ℝ} (hf : LocallyBoundedVariationOn f univ)
    (hp : Function.Periodic f T) {s : ℝ}
    (hs : s ∈ range (variationOnFromTo f univ 0)) :
    naturalParameterization f univ 0 (s + variationOnFromTo f univ 0 T) =
      naturalParameterization f univ 0 s := by
  obtain ⟨t, rfl⟩ := hs
  rw [← lengthParameter_add_period hf hp]
  have heq (x : ℝ) : naturalParameterization f univ 0 (variationOnFromTo f univ 0 x) = f x :=
    edist_eq_zero.mp (edist_naturalParameterization_eq_zero hf (mem_univ 0) (mem_univ x))
  rw [heq, heq, hp]

theorem convex_range_lengthParameter {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ → E} {C : ℝ≥0} (hf : LipschitzWith C f) :
    Convex ℝ (range (variationOnFromTo f univ 0)) := by
  have hc := (lipschitzOnWith_univ.mp
    (lipschitzOnWith_variationOnFromTo hf.lipschitzOnWith (mem_univ 0))).continuous
  exact (isPreconnected_range hc).ordConnected.convex

end PoincareConjecture.M60
