import PoincareLib.Topology.Manifold.NeckCap.Cap.Boundary
import PoincareLib.Geometry.Riemannian.ScalarOperators.Extrema.FiniteRegularity

/-!
# Regularity of a cap core

The regular defining function at each boundary point rules out an isolated
boundary sheet: the closed core is the closure of its interior.

Reference: Morgan--Tian, Definition 9.72, pp. 230--231, and
Proposition A.21, Claims A.23--A.24, pp. 512--513.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)

omit [T2Space M] in
theorem boundary_subset_closure_core : C.boundary_sphere ⊆ closure C.core := by
  intro x hx
  obtain ⟨U, f, hU, hxU, _, hdef, hzero, hf, d, _, hd⟩ :=
    C.boundary_local_defining_function x hx
  by_contra hcl
  have hnonneg : ∀ y ∈ U \ closure C.core, 0 ≤ f y := by
    intro y hy
    by_contra h
    have hfy : f y < 0 := lt_of_not_ge h
    have hfycont : ContinuousAt f y :=
      (hf.continuousOn y hy.1).continuousAt (hU.mem_nhds hy.1)
    have hcore : y ∈ C.core := by
      rw [C.core_eq_interior_closed_core, mem_interior_iff_mem_nhds]
      apply mem_of_superset (inter_mem (hU.mem_nhds hy.1)
        (hfycont.preimage_mem_nhds (Iio_mem_nhds hfy)))
      intro z hz
      exact (hdef z hz.1).mpr (le_of_lt hz.2)
    exact hy.2 (subset_closure hcore)
  have hmin : IsLocalMin f x := by
    filter_upwards [(hU.sdiff isClosed_closure).mem_nhds ⟨hxU, hcl⟩] with y hy
    simpa [hzero] using hnonneg y hy
  have hfs : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) 2 f x :=
    ((hf x hxU).contMDiffAt (hU.mem_nhds hxU)).of_le (by decide)
  have hz := LeviCivitaData.mvfderiv_eq_zero_of_isLocalMax_contMDiffAt hfs.neg hmin.neg
  have heval := congrArg (fun F => F d) hz
  change mvfderiv (𝓡 3) (-f) x d = 0 at heval
  rw [mvfderiv_neg] at heval
  apply hd
  simpa using heval

theorem closure_core_eq_closed_core : closure C.core = C.closed_core := by
  apply Subset.antisymm
  · exact C.isClosed_closed_core.closure_subset_iff.mpr C.core_subset_closed_core
  · rw [C.closed_core_eq_core_union_boundary]
    exact union_subset subset_closure C.boundary_subset_closure_core

theorem frontier_core_eq_boundary : frontier C.core = C.boundary_sphere := by
  rw [frontier, C.closure_core_eq_closed_core, C.isOpen_core.interior_eq,
    C.boundary_eq_closed_core_diff_core]

end PoincareMT.CapCertificate
