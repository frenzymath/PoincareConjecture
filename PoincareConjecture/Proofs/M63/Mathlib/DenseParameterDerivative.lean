import PoincareConjecture.Proofs.M62.Mathlib.ParameterIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

open Set MeasureTheory
open scoped Topology intervalIntegral

universe u v

theorem hasDerivAt_of_dense_parameter_set
    {Z : Type u} [TopologicalSpace Z]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {S D : Set Z} {q v : ℝ × Z → E}
    (hDS : D ⊆ S) (hSD : S ⊆ closure D)
    (hq : ContinuousOn q (univ ×ˢ S)) (hv : ContinuousOn v (univ ×ˢ S))
    (hd : ∀ z ∈ D, ∀ x : ℝ, HasDerivAt (fun y => q (y, z)) (v (x, z)) x) :
    ∀ z ∈ S, ∀ x : ℝ, HasDerivAt (fun y => q (y, z)) (v (x, z)) x := by
  have hvslice (z : Z) (hz : z ∈ S) : Continuous (fun x : ℝ => v (x, z)) :=
    hv.comp_continuous (continuous_id.prodMk continuous_const)
      (fun _ => ⟨mem_univ _, hz⟩)
  have hqslice (y : ℝ) : ContinuousOn (fun z => q (y, z)) S :=
    hq.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hz => ⟨mem_univ _, hz⟩)
  have hprimitive (y : ℝ) : EqOn (fun z => ∫ r in (0 : ℝ)..y, v (r, z))
      (fun z => q (y, z) - q (0, z)) S := by
    have hD : EqOn (fun z => ∫ r in (0 : ℝ)..y, v (r, z))
        (fun z => q (y, z) - q (0, z)) D := by
      intro z hz
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd z hz r)
        ((hvslice z (hDS hz)).intervalIntegrable 0 y)
    exact hD.of_subset_closure (hv.intervalIntegral_prod_left 0 y)
      ((hqslice y).sub (hqslice 0)) hDS hSD
  intro z hz x
  have heq : (fun y => q (y, z)) =
      fun y => q (0, z) + ∫ r in (0 : ℝ)..y, v (r, z) := by
    funext y
    have hi : (∫ r in (0 : ℝ)..y, v (r, z)) = q (y, z) - q (0, z) :=
      hprimitive y hz
    rw [hi]
    abel
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right
    ((hvslice z hz).intervalIntegrable 0 x)
    ((hvslice z hz).stronglyMeasurableAtFilter _ _)
    (hvslice z hz).continuousAt).const_add (q (0, z))
