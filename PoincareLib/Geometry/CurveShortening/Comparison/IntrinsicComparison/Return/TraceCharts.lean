import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Boundary.ArcTopology

/-!
# Actual real charts on the simple return trace

The interval loop descends to an embedded additive circle. Compactness
constructs its inverse on the trace, and the standard circle intervals
then give real charts at every point, including the transverse return.

Context: Morgan--Tian Lemma 19.45, printed p. 474; Proposition 19.35, printed pp.
467-481.
-/

noncomputable section
set_option autoImplicit false

open Set Function
open scoped Topology

namespace PoincareMT

/-- The actual image of the simple closed return loop is homeomorphic to its parameter
circle, with the original parametrization on `[0,T)`. Source/construction:
proof-work/tasks/M64/reports/2026-09-25-return-trace-incidence.md, return-trace chart
construction. -/
theorem m64Intrinsic_return_trace_homeomorph
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ} (hT : 0 < T)
    (hc : ContinuousOn gamma (Icc 0 T)) (hend : gamma 0 = gamma T)
    (hinj : InjOn gamma (Ico 0 T)) :
    ∃ e : AddCircle T ≃ₜ (gamma '' Icc 0 T),
      ∀ t ∈ Ico (0 : ℝ) T, (e (t : AddCircle T)).1 = gamma t := by
  let : Fact (0 < T) := ⟨hT⟩
  let f : AddCircle T → AnnulusCoordinates := AddCircle.liftIco T 0 gamma
  have hfc : Continuous f := AddCircle.liftIco_zero_continuous hend hc
  have hfi : Injective f := by
    intro x y hxy
    apply (AddCircle.equivIco T 0).injective
    apply Subtype.ext
    apply hinj
    · simpa only [zero_add] using (AddCircle.equivIco T 0 x).property
    · simpa only [zero_add] using (AddCircle.equivIco T 0 y).property
    · exact hxy
  have hrange : range f = gamma '' Icc 0 T := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(AddCircle.equivIco T 0 x).1, ?_, rfl⟩
      exact Ico_subset_Icc_self (by
        simpa only [zero_add] using (AddCircle.equivIco T 0 x).property)
    · rintro ⟨t, ht, rfl⟩
      rcases ht.2.eq_or_lt with rfl | htT
      · refine ⟨(0 : ℝ), ?_⟩
        exact (AddCircle.liftIco_zero_coe_apply ⟨le_rfl, hT⟩).trans hend
      · exact ⟨(t : AddCircle T), AddCircle.liftIco_zero_coe_apply ⟨ht.1, htT⟩⟩
  let e := (hfc.isClosedEmbedding hfi).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hrange)
  exact ⟨e, fun t ht => AddCircle.liftIco_zero_coe_apply ht⟩

/-- Every point of the actual trace has a real interval chart. The circle cut is chosen away
from the point, so this includes the return corner without any differentiability assumption
there. Source/construction:
proof-work/tasks/M64/reports/2026-09-25-return-trace-incidence.md, return-trace chart
construction. -/
theorem m64Intrinsic_return_trace_real_charts
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ} (hT : 0 < T)
    (hc : ContinuousOn gamma (Icc 0 T)) (hend : gamma 0 = gamma T)
    (hinj : InjOn gamma (Ico 0 T)) :
    ∀ p : gamma '' Icc 0 T,
      ∃ C : OpenPartialHomeomorph ℝ (gamma '' Icc 0 T), p ∈ C.target := by
  let : Fact (0 < T) := ⟨hT⟩
  obtain ⟨e, _⟩ := m64Intrinsic_return_trace_homeomorph hT hc hend hinj
  intro p
  let t : ℝ := (AddCircle.equivIco T 0 (e.symm p)).1
  let C := AddCircle.openPartialHomeomorphCoe T (t - T / 2)
  have ht : t ∈ C.source := by
    change t ∈ Ioo (t - T / 2) (t - T / 2 + T)
    constructor <;> linarith
  refine ⟨C.trans e.toOpenPartialHomeomorph, ?_⟩
  have hp := C.map_source ht
  have hvalue : C t = e.symm p := AddCircle.coe_equivIco
  rw [hvalue] at hp
  change p ∈ univ ∩ e.symm ⁻¹' C.target
  exact ⟨mem_univ p, hp⟩

end PoincareMT
