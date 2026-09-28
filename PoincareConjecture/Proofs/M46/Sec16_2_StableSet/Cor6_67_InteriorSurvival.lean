import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_SurvivalSlice










set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}



theorem exists_surviving_extension_at_interior
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : 0 < s) (hZ : (Z, s) ∈ E.domain)
    (htime : T - s ^ 2 ∈ interior I.domain) :
    ∃ b : ℝ, s < b ∧ (Z, b) ∈ E.domain := by
  obtain ⟨U, hU, hZU, hUD⟩ := E.domain_relative_open (Z, s) hZ
  have hUtime : {r : ℝ | (Z, r) ∈ U} ∈ 𝓝 s :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds hZU)
  have hphysical : {r : ℝ | T - r ^ 2 ∈ interior I.domain} ∈ 𝓝 s :=
    (continuous_const.sub (continuous_id.pow 2)).continuousAt.preimage_mem_nhds
      (isOpen_interior.mem_nhds htime)
  have hsurvive : {r : ℝ | (Z, r) ∈ E.domain} ∈ 𝓝 s := by
    filter_upwards [hUtime, Ioi_mem_nhds hs, hphysical] with r hrU hrpos hrtime
    exact hUD ⟨hrU, hrpos.le, interior_subset hrtime⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hsurvive
  refine ⟨s + r / 2, by linarith, hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hr)]
  linarith

end PoincareConjecture.Proofs.M46
