import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Set Filter

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

omit [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
set_option backward.isDefEq.respectTransparency false in
private lemma mfderiv_eq_zero_at_local_min {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) f x) (hmin : IsLocalMin f x) :
    mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f x = 0 := by
  have hchart : IsLocalMin (f ∘ (extChartAt (𝓡 3) x).symm)
      ((extChartAt (𝓡 3) x) x) := by
    have htend : Tendsto (extChartAt (𝓡 3) x).symm
        (𝓝 ((extChartAt (𝓡 3) x) x)) (𝓝 x) := by
      simpa only [extChartAt_to_inv] using
        (continuousAt_extChartAt_symm (I := 𝓡 3) x).tendsto
    change ∀ᶠ z in 𝓝 ((extChartAt (𝓡 3) x) x),
      f ((extChartAt (𝓡 3) x).symm ((extChartAt (𝓡 3) x) x)) ≤
        f ((extChartAt (𝓡 3) x).symm z)
    simpa only [extChartAt_to_inv] using htend.eventually hmin
  rw [hf.mfderiv]
  simpa [writtenInExtChartAt, chartAt_self_eq] using hchart.fderiv_eq_zero

theorem closed_core_eq_closure_core (N : CapCertificate g) :
    N.closed_core = closure N.core := by
  apply Subset.antisymm
  · intro x hx
    by_contra hxcl
    have hxnot : x ∉ interior N.closed_core := by
      intro hxi
      exact hxcl (subset_closure (N.core_eq_interior_closed_core.symm ▸ hxi))
    have hxS : x ∈ N.boundary_sphere := by
      rw [← N.core_frontier_eq_boundary]
      exact (mem_frontier_iff_notMem_interior hx).mpr hxnot
    obtain ⟨U, f, hU, hxU, _, hY, hfx, hf, d, _, hd⟩ :=
      N.boundary_local_defining_function x hxS
    have hnonneg : ∀ y ∈ U ∩ (closure N.core)ᶜ, 0 ≤ f y := by
      intro y hy
      by_contra hyneg
      have hylt : f y < 0 := lt_of_not_ge hyneg
      have hfcont := hf.continuousOn.continuousAt (hU.mem_nhds hy.1)
      have hnegative : {z | f z < 0} ∈ 𝓝 y :=
        hfcont.preimage_mem_nhds (Iio_mem_nhds hylt)
      have hyY : y ∈ interior N.closed_core := by
        apply mem_interior_iff_mem_nhds.mpr
        filter_upwards [hU.mem_nhds hy.1, hnegative] with z hzU hzneg
        exact (hY z hzU).mpr (le_of_lt hzneg)
      exact hy.2 (subset_closure (N.core_eq_interior_closed_core.symm ▸ hyY))
    have hmin : IsLocalMin f x := by
      filter_upwards [(hU.inter isClosed_closure.isOpen_compl).mem_nhds
        (show x ∈ U ∩ (closure N.core)ᶜ from ⟨hxU, hxcl⟩)] with y hy
      simpa only [hfx] using hnonneg y hy
    have hzero := mfderiv_eq_zero_at_local_min
      (((hf x hxU).contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp)) hmin
    exact hd (by simp [mvfderiv, hzero])
  · rw [N.core_eq_interior_closed_core]
    exact N.closed_core_compact.isClosed.closure_interior_subset

end PoincareConjecture.CapCertificate
