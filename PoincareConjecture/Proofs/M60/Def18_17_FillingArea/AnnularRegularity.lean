import PoincareConjecture.Proofs.M60.Mathlib.RelativeSmoothing
import PoincareConjecture.Proofs.M58.Cor18_28_DiskLipschitz
import Mathlib.Geometry.Manifold.Metrizable

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem m60_exists_annular_lipschitz_constant
    {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) {F : LoopPlane → M} (hF : Continuous F)
    {r₀ r : ℝ} (hr : r₀ < r)
    (hregular : ∀ z : LoopPlane, r₀ < ‖z‖ → ContMDiffAt (𝓡 2) (𝓡 3) 1 F z) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ loopDiskSet ∩ {z | r ≤ ‖z‖},
      ∀ y ∈ loopDiskSet ∩ {z | r ≤ ‖z‖},
        g.edist (F x) (F y) ≤ ENNReal.ofReal L * ENNReal.ofReal ‖x - y‖ := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace LoopAmbient M
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨G, hG, hEq⟩ := M60.exists_c1_eqOn_compl_of_compact (F := LoopAmbient)
    (⟨F, hF⟩ : C(LoopPlane, M)) (isCompact_closedBall (0 : LoopPlane) r₀)
    (isOpen_ball (x := (0 : LoopPlane)) (ε := r))
    (closedBall_subset_ball hr)
    (fun z hz => hregular z (by
      simpa only [mem_closedBall, dist_zero_right, not_le] using hz))
  obtain ⟨L, hL, hLip⟩ := Proofs.M58.exists_disk_lipschitz_constant g hG
  refine ⟨L, hL, ?_⟩
  intro x hx y hy
  have hx' : x ∈ (ball (0 : LoopPlane) r)ᶜ := by
    simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt, mem_ofPred_eq] using hx.2
  have hy' : y ∈ (ball (0 : LoopPlane) r)ᶜ := by
    simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt, mem_ofPred_eq] using hy.2
  simpa only [hEq hx', hEq hy', ContinuousMap.coe_mk] using hLip ⟨x, hx.1⟩ ⟨y, hy.1⟩

end PoincareConjecture
