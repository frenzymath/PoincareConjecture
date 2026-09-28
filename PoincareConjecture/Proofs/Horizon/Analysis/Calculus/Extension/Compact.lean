import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension










noncomputable section
set_option autoImplicit false
open Filter Set Function
open scoped ContDiff Topology
namespace Poincare.Analysis



theorem exists_contDiff_extension_near_compact
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : X → E) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ (F : X → E) (V : Set X),
      ContDiff ℝ ∞ F ∧ IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ EqOn F f V := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨V, hV, hLV, hVU⟩ := hL.exists_isOpen_closure_subset
    (hU.mem_nhdsSet.mpr hLU)
  obtain ⟨a, ha, had, har⟩ := hV.exists_contDiff_support_eq (n := ⊤)
  obtain ⟨b, hb, hbd, hbr⟩ := hL.isClosed.isOpen_compl.exists_contDiff_support_eq (n := ⊤)
  have hab (x : X) : 0 < a x + b x := by
    have hax := (har (mem_range_self x)).1
    have hbx := (hbr (mem_range_self x)).1
    by_cases hx : x ∈ L
    · have hane : a x ≠ 0 := by
        rw [← mem_support, ha]
        exact hLV hx
      exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hax hane.symm) hbx
    · have hbne : b x ≠ 0 := by
        rwa [← mem_support, hb]
      exact add_pos_of_nonneg_of_pos hax (lt_of_le_of_ne hbx hbne.symm)
  let c : X → ℝ := fun x => a x / (a x + b x)
  have hc : ContDiff ℝ ∞ c := had.div (had.add hbd) (fun x => (hab x).ne')
  have hcs : tsupport c ⊆ U := by
    apply (closure_mono (show support c ⊆ V from ?_)).trans hVU
    intro x hx
    rw [← ha]
    exact fun h => hx (by simp [c, h])
  have hcL : EqOn c (fun _ => 1) L := by
    intro x hx
    have hbx : b x = 0 := by
      rw [← notMem_support, hb]
      exact not_not_intro hx
    simp only [c, hbx, add_zero]
    exact div_self (by simpa [hbx] using (hab x).ne')
  refine ⟨fun x => c x • f x, interior L, ?_, isOpen_interior, hKL,
    interior_subset.trans hLU, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport c
    · exact hc.contDiffAt.smul ((hf x (hcs hx)).contDiffAt (hU.mem_nhds (hcs hx)))
    · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [Pi.zero_apply] at hy
      simp only [hy, zero_smul]
  · intro x hx
    simp only [hcL (interior_subset hx), one_smul]

end Poincare.Analysis
