import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.DiscreteSubset

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace Poincare.Analysis

theorem critical_values_null_of_differentiableOn {f : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℝ f U) :
    volume (f '' {x ∈ U | deriv f x = 0}) = 0 := by
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (f' := fun _ => (0 : ℝ →L[ℝ] ℝ)) volume
  · intro x hx
    have hd := ((hf x hx.1).differentiableAt (hU.mem_nhds hx.1)).hasDerivAt
    rw [hx.2] at hd
    simpa using hd.hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    simp

theorem exists_simultaneous_regular_value_avoiding_finite
    {ι : Type*} [Finite ι] (f : ι → ℝ → ℝ) (U : ι → Set ℝ)
    (hU : ∀ i, IsOpen (U i)) (hf : ∀ i, DifferentiableOn ℝ (f i) (U i))
    (s : Finset ℝ) {a b : ℝ} (hab : a < b) :
    ∃ c ∈ Ioo a b, c ∉ s ∧
      ∀ i x, x ∈ U i → f i x = c → deriv (f i) x ≠ 0 := by
  classical
  let C (i : ι) : Set ℝ := (f i) '' {x ∈ U i | deriv (f i) x = 0}
  have hC : ∀ i, volume (C i) = 0 := fun i =>
    critical_values_null_of_differentiableOn (hU i) (hf i)
  have hnull : volume ((⋃ i, C i) ∪ (↑s : Set ℝ)) = 0 :=
    measure_union_null (measure_iUnion_null hC) (s.finite_toSet.measure_zero volume)
  have hnot : ¬ Ioo a b ⊆ (⋃ i, C i) ∪ (↑s : Set ℝ) := by
    intro hsub
    exact (isOpen_Ioo.measure_pos volume (nonempty_Ioo.mpr hab)).ne'
      (measure_mono_null hsub hnull)
  obtain ⟨c, hc, hbad⟩ := Set.not_subset.mp hnot
  refine ⟨c, hc, fun hcs => hbad (Or.inr hcs), ?_⟩
  intro i x hx hfx hzero
  exact hbad (Or.inl (mem_iUnion.mpr ⟨i, x, ⟨hx, hzero⟩, hfx⟩))

theorem finite_regular_fiber_Icc {f : ℝ → ℝ} {a b y : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hd : DifferentiableOn ℝ f (Ioo a b))
    (hleft : f a ≠ y) (hright : f b ≠ y)
    (hregular : ∀ t ∈ Ioo a b, f t = y → deriv f t ≠ 0) :
    {t | t ∈ Icc a b ∧ f t = y}.Finite := by
  let S : Set ℝ := {t | t ∈ Icc a b ∧ f t = y}
  have hclosed : IsClosed S := isClosed_Icc.isClosed_eq hf continuousOn_const
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed (fun _ ht => ht.1)
  apply hcompact.finite
  apply isDiscrete_iff_nhdsNE.mpr
  intro t ht
  have ht' : t ∈ Ioo a b := by
    constructor
    · exact lt_of_le_of_ne ht.1.1 (fun h => hleft (h ▸ ht.2))
    · exact lt_of_le_of_ne ht.1.2 (fun h => hright (h ▸ ht.2))
  have hdt := (hd t ht').differentiableAt (isOpen_Ioo.mem_nhds ht')
  apply inf_principal_eq_bot.mpr
  filter_upwards [hdt.hasDerivAt.eventually_ne (c := y) (hregular t ht' ht.2)] with s hs
  exact fun hsS => hs hsS.2

theorem exists_simultaneous_finite_regular_fibers
    {ι : Type*} [Finite ι] (f : ι → ℝ → ℝ) (l r : ι → ℝ)
    (hf : ∀ i, ContinuousOn (f i) (Icc (l i) (r i)))
    (hd : ∀ i, DifferentiableOn ℝ (f i) (Ioo (l i) (r i)))
    (s : Finset ℝ) {a b : ℝ} (hab : a < b) :
    ∃ c ∈ Ioo a b, c ∉ s ∧ ∀ i,
      f i (l i) ≠ c ∧ f i (r i) ≠ c ∧
      {t | t ∈ Icc (l i) (r i) ∧ f i t = c}.Finite ∧
      ∀ t ∈ Ioo (l i) (r i), f i t = c → deriv (f i) t ≠ 0 := by
  classical
  let := Fintype.ofFinite ι
  let forbidden := s ∪ (Finset.univ.image (fun i => f i (l i)) ∪
    Finset.univ.image (fun i => f i (r i)))
  obtain ⟨c, hc, havoid, hregular⟩ := exists_simultaneous_regular_value_avoiding_finite
    f (fun i => Ioo (l i) (r i)) (fun _ => isOpen_Ioo) hd forbidden hab
  have hleft (i : ι) : f i (l i) ≠ c := by
    intro h
    apply havoid
    have hmem : f i (l i) ∈ forbidden := by simp [forbidden]
    exact h ▸ hmem
  have hright (i : ι) : f i (r i) ≠ c := by
    intro h
    apply havoid
    have hmem : f i (r i) ∈ forbidden := by simp [forbidden]
    exact h ▸ hmem
  refine ⟨c, hc, fun hcs => havoid (Finset.mem_union_left _ hcs), fun i =>
    ⟨hleft i, hright i, ?_, hregular i⟩⟩
  exact finite_regular_fiber_Icc (hf i) (hd i) (hleft i) (hright i) (hregular i)

end Poincare.Analysis
