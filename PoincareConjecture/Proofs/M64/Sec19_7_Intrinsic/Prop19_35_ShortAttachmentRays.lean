import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapBandEndpointCoverage

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology

namespace PoincareConjecture

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

end PoincareConjecture
