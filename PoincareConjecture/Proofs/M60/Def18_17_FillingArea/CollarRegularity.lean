import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.AnnularRegularity
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.DiskRescaling
import Mathlib.Topology.Piecewise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology Pointwise

universe u

namespace PoincareConjecture

theorem m60_exists_collar_lipschitz_of_matching_disk
    {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) {γ : C1FreeLoopSpace (M := M)}
    (D : LipschitzSpanningDisk g γ) (H : LoopPlane → M)
    {rho r : ℝ} (hrho : 0 < rho) (hr : rho < r)
    (hmatch : ∀ z : LoopPlane, ‖z‖ = rho → D.map (rho⁻¹ • z) = H z)
    (hH : ∀ z : LoopPlane, rho ≤ ‖z‖ → ContMDiffAt (𝓡 2) (𝓡 3) 1 H z) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ loopDiskSet ∩ {z | r ≤ ‖z‖},
      ∀ y ∈ loopDiskSet ∩ {z | r ≤ ‖z‖},
        g.edist (H x) (H y) ≤ ENNReal.ofReal L * ENNReal.ofReal ‖x - y‖ := by
  classical
  let F := (closedBall (0 : LoopPlane) rho).piecewise (fun z => D.map (rho⁻¹ • z)) H
  have hin : MapsTo (fun z : LoopPlane => rho⁻¹ • z) (closedBall 0 rho) loopDiskSet := by
    intro z hz
    rw [← m60_inv_smul_closedBall hrho]
    exact smul_mem_smul_set hz
  have hinner : ContinuousOn (fun z : LoopPlane => D.map (rho⁻¹ • z))
      (closure (closedBall 0 rho)) := by
    rw [isClosed_closedBall.closure_eq]
    exact D.continuous_on_disk.comp
      (show Continuous (fun z : LoopPlane => rho⁻¹ • z) from
        continuous_id.const_smul rho⁻¹).continuousOn hin
  have houter : closure (closedBall (0 : LoopPlane) rho)ᶜ ⊆ {z | rho ≤ ‖z‖} := by
    apply closure_minimal _ (isClosed_le continuous_const continuous_norm)
    intro z hz
    exact (show rho < ‖z‖ from by
      simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hz).le
  have hF : Continuous F := continuous_piecewise
    (fun z hz => hmatch z (by
      simpa only [mem_sphere, dist_zero_right] using frontier_closedBall_subset_sphere hz))
    hinner (fun z hz => (hH z (houter hz)).continuousAt.continuousWithinAt)
  have heq {z : LoopPlane} (hz : rho < ‖z‖) : F =ᶠ[𝓝 z] H := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    exact piecewise_eq_of_notMem _ _ _ (by
      simpa only [mem_closedBall, dist_zero_right, not_le] using hw)
  obtain ⟨L, hL, hLip⟩ := m60_exists_annular_lipschitz_constant g hF hr
    (fun z hz => (hH z hz.le).congr_of_eventuallyEq (heq hz))
  refine ⟨L, hL, ?_⟩
  intro x hx y hy
  have hxH : F x = H x := (heq (hr.trans_le hx.2)).eq_of_nhds
  have hyH : F y = H y := (heq (hr.trans_le hy.2)).eq_of_nhds
  simpa only [hxH, hyH] using hLip x hx y hy

end PoincareConjecture
