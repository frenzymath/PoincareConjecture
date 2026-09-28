import PoincareConjecture.Proofs.M46.Sec16_1_MinimizingRegion.CompactMinima









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  {T start : ℝ} {x : G.Point}





theorem minimizingRegion_nonempty_of_slice_comparison
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (LG : GeneralizedLGeometryConclusion G) (E : M14ExponentialFamily G T x)
    (C : ActionConfinement G T start x) (hstrip : Icc start T ⊆ I.domain)
    (hcontinuous : ∀ a c : ℝ, 0 < a → c ^ 2 ≤ T - start →
      ContinuousOn (cappedSliceAction G T x C.barrier) (Icc a c))
    (hbound : ∀ b : ℝ, 0 < b → b ^ 2 ≤ T - start →
      cappedSliceAction G T x C.barrier b ≤ 3 * b) :
    Nonempty (MinimizingRegion G T start x C) := by
  obtain ⟨U, hU, hregion⟩ := confinementRegion_relatively_open hM12 LG E C hstrip
  refine ⟨{
    region := confinementRegion C
    region_exact := fun _ => Iff.rfl
    time_mem := fun _ hy => hy.1
    relatively_open := ⟨U, hU, hregion⟩
    minimizing := ?_
    slice_minimum := ?_
    compact_minima := confinementRegion_compact_minima hM04 hM12 LG E C hstrip hcontinuous hbound }⟩
  · rintro y ⟨hyt, p0, hp0⟩
    exact actionConfinement_attained hM12 C (sub_pos.mpr hyt.2)
      (sub_le_sub_left hyt.1 T) p0 hp0
  · intro t ht
    let b := Real.sqrt (T - t)
    have hb : 0 < b := Real.sqrt_pos.mpr (sub_pos.mpr ht.2)
    have hbsq : b ^ 2 = T - t := Real.sq_sqrt (sub_nonneg.mpr ht.2.le)
    have hbStart : b ^ 2 ≤ T - start := by rw [hbsq]; exact sub_le_sub_left ht.1 T
    have hbMax : b ≤ Real.sqrt (T - start) := Real.sqrt_le_sqrt (sub_le_sub_left ht.1 T)
    have hvalue : cappedSliceAction G T x C.barrier b < C.barrier :=
      (hbound b hb hbStart).trans_lt
        ((mul_le_mul_of_nonneg_left hbMax (by norm_num : (0 : ℝ) ≤ 3)).trans_lt C.barrier_large)
    obtain ⟨y, hy, hyt, hyvalue, hminimum⟩ :=
      confinementRegion_exists_slice_minimum hM04 hM12 LG E C hb hbStart hvalue
    have hbt : T - b ^ 2 = t := by rw [hbsq]; ring
    refine ⟨y, hy, hyt.trans hbt, ?_, ?_⟩
    · rw [← hbsq, hyvalue]
      simpa only [Real.sqrt_sq hb.le] using hbound b hb hbStart
    · intro z hz hzt
      rw [← hbsq]
      exact hminimum z hz (hzt.trans hbt.symm)

end PoincareConjecture.Proofs.M46
