import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.Radial.Parameters
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.BoundedCylinder

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

def quadraticMinimumRadius (v : E3) (p : S2) : Real :=
  if inner Real v (p : E3) < 0 then minimumCapLowerRadius (inner Real v (p : E3))
  else boundedCylinderRadius v p

private theorem sphere_height_mem {v : E3} (hv : ‖v‖ = 1) (p : S2) :
    inner Real v (p : E3) ∈ Icc (-1 : Real) 1 := by
  apply abs_le.mp
  simpa [hv] using abs_real_inner_le_norm v (p : E3)

theorem quadraticMinimumRadius_pos {v : E3} (hv : ‖v‖ = 1) (p : S2) :
    0 < quadraticMinimumRadius v p := by
  unfold quadraticMinimumRadius
  split_ifs with hp
  · exact minimumCapLowerRadius_pos ⟨(sphere_height_mem hv p).1, hp.le⟩
  · exact boundedCylinderRadius_pos v p

theorem quadraticMinimumRadius_eq_north {v : E3} (p : S2)
    (hp : 0 ≤ inner Real v (p : E3)) :
    quadraticMinimumRadius v p = boundedCylinderRadius v p :=
  if_neg (not_lt_of_ge hp)

theorem quadraticMinimumRadius_eq_cylinder {v : E3} (p : S2)
    (hp : inner Real v (p : E3) ∈ Ioo (-9 / 11 : Real) (1 / 2)) :
    quadraticMinimumRadius v p = (Real.sqrt (1 - inner Real v (p : E3) ^ 2))⁻¹ := by
  unfold quadraticMinimumRadius
  split_ifs with hn
  · exact minimumCapLowerRadius_eq_cylinder hp.1
  · exact boundedCylinderRadius_of_abs_height_le v p
      (abs_le.mpr ⟨by linarith, hp.2.le⟩)

theorem quadraticMinimumRadius_eq_rayFactor {v : E3} (p : S2)
    (hp : inner Real v (p : E3) < -3 / 4) :
    quadraticMinimumRadius v p = minimumCapRayFactor (inner Real v (p : E3)) := by
  rw [quadraticMinimumRadius, if_pos (by linarith)]
  unfold minimumCapLowerRadius
  split_ifs with hl
  · rfl
  · exact (minimumCapRayFactor_eq_cylinder ⟨by linarith, hp⟩).symm

theorem contMDiff_quadraticMinimumRadius {v : E3} (hv : ‖v‖ = 1) :
    ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (quadraticMinimumRadius v) := by
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun p : S2 => inner Real v (p : E3)) :=
    (innerSL Real v).contMDiff.comp (fun p => contMDiff_coe_sphere (n := 2) p)
  intro p
  by_cases hp : inner Real v (p : E3) < 0
  · have hs : ContMDiffAt (𝓡 2) 𝓘(Real, Real) ∞
        (fun q : S2 => minimumCapLowerRadius (inner Real v (q : E3))) p :=
      (contDiffAt_minimumCapLowerRadius
        ⟨by linarith [(sphere_height_mem hv p).1], by linarith⟩).contMDiffAt.comp p (hh p)
    apply hs.congr_of_eventuallyEq
    filter_upwards [(hh p).continuousAt.eventually (gt_mem_nhds hp)] with q hq
    exact if_pos hq
  · by_cases hp0 : 0 < inner Real v (p : E3)
    · apply (contMDiff_boundedCylinderRadius v p).congr_of_eventuallyEq
      filter_upwards [(hh p).continuousAt.eventually (lt_mem_nhds hp0)] with q hq
      exact if_neg (not_lt_of_ge hq.le)
    · have heq : inner Real v (p : E3) = 0 := le_antisymm (le_of_not_gt hp0) (le_of_not_gt hp)
      apply (contMDiff_boundedCylinderRadius v p).congr_of_eventuallyEq
      have hn : ∀ᶠ q : S2 in 𝓝 p, inner Real v (q : E3) ∈ Ioo (-1 / 2 : Real) (1 / 2) :=
        (hh p).continuousAt.eventually (isOpen_Ioo.mem_nhds (by
          change inner Real v (p : E3) ∈ Ioo (-1 / 2 : Real) (1 / 2)
          rw [heq]
          norm_num))
      filter_upwards [hn] with q hq
      rw [quadraticMinimumRadius_eq_cylinder q ⟨by linarith [hq.1], hq.2⟩,
        boundedCylinderRadius_of_abs_height_le v q (abs_le.mpr ⟨by linarith [hq.1], hq.2.le⟩)]

theorem exists_quadraticMinimum_radial_ambient {v : E3} (hv : ‖v‖ = 1) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, F y = y) ∧
      (∀ p : S2, F p = quadraticMinimumRadius v p • (p : E3)) ∧
      (∀ p : S2, 0 ≤ inner Real v (p : E3) →
        F p = boundedCylinderRadius v p • (p : E3)) ∧
      frontier (F '' closedBall (0 : E3) 1) = F '' sphere (0 : E3) 1 := by
  obtain ⟨F, hsupport, hF⟩ := exists_radial_sphere_extension (quadraticMinimumRadius v)
    (contMDiff_quadraticMinimumRadius hv) (quadraticMinimumRadius_pos hv)
  refine ⟨F, hsupport, hF, ?_, ?_⟩
  · intro p hp
    rw [hF, quadraticMinimumRadius_eq_north p hp]
  · change frontier (F.toHomeomorph '' closedBall (0 : E3) 1) =
      F.toHomeomorph '' sphere (0 : E3) 1
    rw [← F.toHomeomorph.image_frontier, frontier_closedBall (0 : E3) (by norm_num : (1 : Real) ≠ 0)]

end Poincare.Manifold.Schoenflies
