import PoincareConjecture.Statements.M14GeneralizedLGeometry
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Geometry.Manifold.ContMDiff.Atlas









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}




theorem exists_chartProductLipschitzOn_of_contMDiffAt {f : G.Point → ℝ}
    {q : G.Point} (hf : ContMDiffAt (spacetimeModel n) 𝓘(ℝ) 1 f q)
    {N : Set G.Point} (hN : N ∈ 𝓝 q) :
    ∃ U : Set G.Point, IsOpen U ∧ q ∈ U ∧ U ⊆ N ∧
      M14ChartProductLipschitzOn G f q U := by
  let e := extChartAt (spacetimeModel n) q
  have hc : ContDiffWithinAt ℝ 1 (fun z => f (e.symm z)) (range (spacetimeModel n)) (e q) := by
    simpa only [writtenInExtChartAt, extChartAt_model_space_eq_id, Function.comp_def,
      PartialEquiv.refl_coe, id_eq] using (contMDiffAt_iff.mp hf).2
  obtain ⟨K, V, hV, hLip⟩ := hc.exists_lipschitzOnWith (spacetimeModel n).convex_range
  obtain ⟨B, hB, hqB, hBsub⟩ := mem_nhdsWithin.mp hV
  have hpre : e ⁻¹' B ∈ 𝓝 q :=
    (continuousAt_extChartAt q).preimage_mem_nhds (hB.mem_nhds hqB)
  obtain ⟨U, hUsub, hU, hqU⟩ := mem_nhds_iff.mp
    (inter_mem hN (inter_mem (extChartAt_source_mem_nhds (I := spacetimeModel n) q) hpre))
  refine ⟨U, hU, hqU, fun z hz => (hUsub hz).1,
    hU, hqU, fun z hz => (hUsub hz).2.1, K, K.coe_nonneg, ?_⟩
  intro z hz w hw
  have hzV : e z ∈ V := hBsub ⟨(hUsub hz).2.2, ⟨(chartAt _ q) z, rfl⟩⟩
  have hwV : e w ∈ V := hBsub ⟨(hUsub hw).2.2, ⟨(chartAt _ q) w, rfl⟩⟩
  have h := hLip.dist_le_mul (e z) hzV (e w) hwV
  simpa only [e.left_inv (hUsub hz).2.1, e.left_inv (hUsub hw).2.1,
    dist_eq_norm, Real.norm_eq_abs] using h

end PoincareConjecture.M14
