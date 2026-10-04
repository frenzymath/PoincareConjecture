import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Jordan.Region
import Mathlib.Topology.Order.Compact

/-!
# Confinement of the bounded focusing region

Radial perturbations put the nonzero extreme radii of a compact planar
region on its frontier. A frontier in the standard annulus therefore
confines the whole region when the origin belongs to its exterior.

Morgan--Tian context: Claim 19.40, printed pp. 470-471, in the proof of Proposition
19.35. The project construction retains the actual constrained path and its boundary
contacts.
-/

noncomputable section
set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace PoincareMT

/-- A compact coordinate region whose frontier lies in the annulus also lies in the annulus,
provided that it does not enclose the origin. This last condition is retained explicitly
rather than inferred from its trace. Source: MT Claim 19.40, pp. 470-471;
`proof-work/tasks/M64/reports/2026-09-24-intrinsic-radial-scalar.md`, Constructed compact
regions from boundary arcs. -/
theorem m64Intrinsic_compact_region_subset_annulus
    {K : Set AnnulusCoordinates} (hK : IsCompact K) (hzero : (0 : AnnulusCoordinates) ∉ K)
    (hfrontier : frontier K ⊆ standardAnnulusDomain) : K ⊆ standardAnnulusDomain := by
  intro x hx
  change 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2
  constructor
  · by_contra hlow
    have hxlow : ‖x‖ < 1 := lt_of_not_ge hlow
    obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn ⟨x, hx⟩ continuous_norm.continuousOn
    have hplow : ‖p‖ < 1 := (hmin hx).trans_lt hxlow
    have hpzero : p ≠ 0 := fun h => hzero (h ▸ hp)
    have hpnormal : 0 < ‖p‖ := norm_pos_iff.mpr hpzero
    have hpint : p ∈ interior K := by
      by_contra hnot
      have h := hfrontier ⟨subset_closure hp, hnot⟩
      exact (not_le.mpr hplow) h.1
    have hsc : Continuous (fun t : ℝ => t • p) := continuous_id.smul continuous_const
    have hnear : (fun t : ℝ => t • p) ⁻¹' K ∈ 𝓝 (1 : ℝ) :=
      hsc.continuousAt.preimage_mem_nhds (by
        simpa only [one_smul] using mem_interior_iff_mem_nhds.mp hpint)
    obtain ⟨d, hd, hdK⟩ := Metric.mem_nhds_iff.mp hnear
    let e := min (d / 2) (1 / 2)
    have he : 0 < e := lt_min (half_pos hd) (by norm_num)
    have he' : e < d := (min_le_left _ _).trans_lt (by linarith)
    have he1 : e < 1 := (min_le_right _ _).trans_lt (by norm_num)
    have hpt : (1 - e) • p ∈ K := by
      apply hdK
      change |1 - e - 1| < d
      rw [show 1 - e - 1 = -e by ring, abs_neg, abs_of_pos he]
      exact he'
    have h := hmin hpt
    change ‖p‖ ≤ ‖(1 - e) • p‖ at h
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr he1)] at h
    nlinarith [mul_pos he hpnormal]
  · by_contra hhigh
    have hxhigh : 2 < ‖x‖ := lt_of_not_ge hhigh
    obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ continuous_norm.continuousOn
    have hphigh : 2 < ‖p‖ := hxhigh.trans_le (hmax hx)
    have hpint : p ∈ interior K := by
      by_contra hnot
      have h := hfrontier ⟨subset_closure hp, hnot⟩
      exact (not_le.mpr hphigh) h.2
    have hsc : Continuous (fun t : ℝ => t • p) := continuous_id.smul continuous_const
    have hnear : (fun t : ℝ => t • p) ⁻¹' K ∈ 𝓝 (1 : ℝ) :=
      hsc.continuousAt.preimage_mem_nhds (by
        simpa only [one_smul] using mem_interior_iff_mem_nhds.mp hpint)
    obtain ⟨d, hd, hdK⟩ := Metric.mem_nhds_iff.mp hnear
    have hpt : (1 + d / 2) • p ∈ K := by
      apply hdK
      change |1 + d / 2 - 1| < d
      rw [show 1 + d / 2 - 1 = d / 2 by ring, abs_of_pos (half_pos hd)]
      linarith
    have h := hmax hpt
    change ‖(1 + d / 2) • p‖ ≤ ‖p‖ at h
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + d / 2)] at h
    nlinarith [mul_pos (half_pos hd) (by linarith : 0 < ‖p‖)]

/-- The closure of an open Jordan region is confined to the annulus when its actual frontier
is and its exterior contains the origin. Source: MT Claim 19.40, pp. 470-471;
`proof-work/tasks/M64/reports/2026-09-24-intrinsic-radial-scalar.md`, Constructed compact
regions from boundary arcs. -/
theorem m64Intrinsic_jordan_closure_subset_annulus
    {U : Set AnnulusCoordinates} (hcompact : IsCompact (closure U))
    (hzero : (0 : AnnulusCoordinates) ∉ closure U)
    (hfrontier : frontier U ⊆ standardAnnulusDomain) :
    closure U ⊆ standardAnnulusDomain :=
  m64Intrinsic_compact_region_subset_annulus hcompact hzero
    (frontier_closure_subset.trans hfrontier)

end PoincareMT
