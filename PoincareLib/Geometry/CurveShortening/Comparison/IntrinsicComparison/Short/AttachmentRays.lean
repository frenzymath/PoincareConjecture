import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Cap.BandEndpointCoverage

/-!
# Choosing short physical attachment cuts

The two endpoint neighborhoods are fixed before choosing band lengths.
Continuity of the actual rays gives one positive bound for both cuts.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481, including Claim 19.40,
pp. 470-471. These project constructions provide actual fitted boundary pieces and
contacts for the regional Gauss--Bonnet arguments.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology

namespace PoincareMT

/-- A sufficiently short closed physical ray segment lies in a prescribed open neighborhood
of its base. Source: `proof-work/tasks/M64/reports/2026-09-24-short-cap-band-join.md`. -/
theorem m64Intrinsic_exists_short_ray_in_neighborhood
    (p d : AnnulusCoordinates) {N : Set AnnulusCoordinates}
    (hN : IsOpen N) (hp : p ∈ N) :
    ∃ delta > 0, (fun u : ℝ => p + u • d) '' Icc (0 : ℝ) delta ⊆ N := by
  have hc : Continuous (fun u : ℝ => p + u • d) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hpre : (fun u : ℝ => p + u • d) ⁻¹' N ∈ 𝓝 (0 : ℝ) := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa only [zero_smul, add_zero] using hN.mem_nhds hp
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨epsilon / 2, half_pos hepsilon, ?_⟩
  rintro z ⟨u, hu, rfl⟩
  apply hball
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hu.1] using
    hu.2.trans_lt (half_lt_self hepsilon)

end PoincareMT
