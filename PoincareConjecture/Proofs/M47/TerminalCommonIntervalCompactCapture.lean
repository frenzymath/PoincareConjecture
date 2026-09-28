import PoincareConjecture.Proofs.M47.TerminalCommonIntervalGlobalIsometry
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M47

theorem terminalCommonInterval_uniform_on_compacts_of_balls
    {M N : Type*} [MetricSpace M] [UniformSpace N]
    (p : M) {f : ℕ → M → N} {F : M → N}
    (hball : ∀ j : ℕ, TendstoUniformlyOn f F atTop (Metric.closedBall p (j + 1)))
    {K : Set M} (hK : IsCompact K) : TendstoUniformlyOn f F atTop K := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall p
  obtain ⟨j, hj⟩ := exists_nat_gt R
  apply (hball j).mono
  exact hR.trans (Metric.closedBall_subset_closedBall (by linarith))

theorem terminalCommonInterval_compact_image_capture
    {M N : Type*} [TopologicalSpace M] [MetricSpace N] [LocallyCompactSpace N]
    {K : Set M} (hK : IsCompact K) {V : Set N} (hV : IsOpen V)
    {f : ℕ → M → N} {F : M → N} (hF : ContinuousOn F K)
    (hmap : MapsTo F K V) (hconv : TendstoUniformlyOn f F atTop K) :
    ∃ L : Set N, IsCompact L ∧ L ⊆ V ∧ ∀ᶠ n in atTop, MapsTo (f n) K L := by
  have himage : IsCompact (F '' K) := hK.image_of_continuousOn hF
  obtain ⟨W, hW, hKW, hWV, hcompact⟩ :=
    exists_open_between_and_isCompact_closure himage hV (mapsTo_iff_image_subset.mp hmap)
  obtain ⟨delta, hdelta, hthick⟩ := himage.exists_thickening_subset_open hW hKW
  refine ⟨closure W, hcompact, hWV, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv delta hdelta] with n hn x hx
  apply subset_closure
  apply hthick
  apply Metric.mem_thickening_iff.mpr
  exact ⟨F x, mem_image_of_mem F hx, by simpa only [dist_comm] using hn x hx⟩

end PoincareConjecture.M47
