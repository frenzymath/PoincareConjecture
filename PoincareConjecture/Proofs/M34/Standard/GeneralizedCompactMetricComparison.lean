import PoincareConjecture.Proofs.M34.Standard.GeneralizedCompactMetricComparisonCoordinates

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.GeneralizedBlowupConvergence

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (C : GeneralizedBlowupConvergence S J)

local instance : TopologicalSpace C.limit.carrier.carrier := C.limit.carrier.topologicalSpace
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.limit.carrier.carrier :=
  C.limit.carrier.chartedSpace
local instance : IsManifold (𝓡 3) ∞ C.limit.carrier.carrier := C.limit.carrier.isManifold

theorem eventually_pullback_inner_comparison_zero
    {K : Set C.limit.sliceCarrier.carrier} (hK : IsCompact K) :
    let h0 : ∀ k, 0 ∈ Icc (-C.exhaustion.time k) 0 :=
      fun k => ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩
    ∀ᶠ k : ℕ in atTop, K ⊆ C.exhaustion.space k ∧
      ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
        (1 / 2 : ℝ) * (C.limit.flow.metric 0).inner x v v ≤
          (C.embedding k).pullbackInner 0 (h0 k) x v v ∧
        (C.embedding k).pullbackInner 0 (h0 k) x v v ≤
          2 * (C.limit.flow.metric 0).inner x v v := by
  classical
  let h0 : ∀ k, 0 ∈ Icc (-C.exhaustion.time k) 0 :=
    fun k => ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩
  have hlocal (q : C.limit.sliceCarrier.carrier) :
      ∃ V : Set C.limit.sliceCarrier.carrier, V ∈ 𝓝 q ∧
        ∀ᶠ k : ℕ in atTop, ∀ x ∈ V, ∀ v : TangentSpace (𝓡 3) x,
          (1 / 2 : ℝ) * (C.limit.flow.metric 0).inner x v v ≤
            (C.embedding k).pullbackInner 0 (h0 k) x v v ∧
          (C.embedding k).pullbackInner 0 (h0 k) x v v ≤
            2 * (C.limit.flow.metric 0).inner x v v := by
    let c := extChartAt (𝓡 3) q
    obtain ⟨H, hH, hqH, hHt⟩ := exists_compact_subset
      (isOpen_extChartAt_target (I := 𝓡 3) q) (mem_extChartAt_target (I := 𝓡 3) q)
    let V := c.source ∩ c ⁻¹' H
    have hV : V ∈ 𝓝 q := inter_mem
      (extChartAt_source_mem_nhds (I := 𝓡 3) q)
      ((continuousAt_extChartAt (I := 𝓡 3) q).preimage_mem_nhds
        (mem_interior_iff_mem_nhds.mp hqH))
    refine ⟨V, hV, ?_⟩
    filter_upwards [C.eventually_chart_pullback_inner_comparison_zero q hH hHt]
      with k hk x hx v
    have hximage : x ∈ c.symm '' H := ⟨c x, hx.2, c.left_inv hx.1⟩
    obtain ⟨y, hy, rfl⟩ := hximage
    have hi : (mfderiv (𝓡 3) (𝓡 3) c.symm y).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm (hHt hy)
    obtain ⟨w, rfl⟩ := hi.surjective v
    exact hk.2 y hy w
  choose V hV hbound using hlocal
  obtain ⟨s, _, hcover⟩ := hK.elim_nhds_subcover V (fun q _ => hV q)
  obtain ⟨j, hj⟩ := C.exists_exhaustion_superset hK
  filter_upwards [s.eventually_all.mpr (fun q _ => hbound q), eventually_ge_atTop j]
    with k hk hjk
  refine ⟨hj.trans (C.exhaustion.space_increasing hjk), ?_⟩
  intro x hx v
  obtain ⟨q, hqs, hxq⟩ : ∃ q ∈ s, x ∈ V q := by
    simpa only [mem_iUnion, exists_prop] using hcover hx
  exact hk q hqs x hxq v

end PoincareConjecture.GeneralizedBlowupConvergence
