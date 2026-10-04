import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Regularity.Continuity.ContactBounds
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Regularity.AlmostEverywhere.RegularGerms
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Regularity.Continuity.ContactBounds
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.CanonicalGeometry.CapPersistenceNormalization

/-!
# The regular core is the closure of its interior

The nonzero differential of the actual local defining function excludes
a local minimum at the boundary. This supplies the interior side needed
by same-core recutting in Morgan-Tian Proposition 9.79(3), p. 234, and
Theorem 12.28, pp. 323-324; cap-persistence-implementation.md, section 2.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M34

/-- A regular local sublevel boundary is approached by interior points.
The dimension is arbitrary and only the actual differential at the
tested point is required (cap recutting, Proposition 9.79(3)). -/
theorem mem_closure_interior_of_local_regular_sublevel
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {U Y : Set M} {f : M → ℝ} {x : M}
    (hU : IsOpen U) (hx : x ∈ U)
    (hsub : ∀ y ∈ U, y ∈ Y ↔ f y ≤ 0) (hzero : f x = 0)
    (hc : ContinuousOn f U) (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hd : mvfderiv (𝓡 n) f x ≠ 0) : x ∈ closure (interior Y) := by
  have hnear : x ∈ closure (U ∩ {y | f y < 0}) := by
    by_contra hnot
    have hn : ∀ᶠ y in 𝓝 x, y ∉ closure (U ∩ {z | f z < 0}) :=
      isClosed_closure.isOpen_compl.mem_nhds hnot
    have hmin : IsLocalMin f x := by
      filter_upwards [hU.mem_nhds hx, hn] with y hy hny
      rw [hzero]
      exact le_of_not_gt (fun hlt => hny (subset_closure ⟨hy, hlt⟩))
    exact hd (M10.mvfderiv_eq_zero_of_isLocalMin hf hmin)
  apply closure_mono (t := interior Y) ?_ hnear
  rintro y ⟨hy, hfy⟩
  apply mem_interior_iff_mem_nhds.mpr
  have hfn : ∀ᶠ z in 𝓝 y, f z < 0 :=
    ((hc y hy).continuousAt (hU.mem_nhds hy)) (isOpen_Iio.mem_nhds hfy)
  filter_upwards [hU.mem_nhds hy, hfn] with z hz hfz
  exact (hsub z hz).mpr hfz.le

end PoincareMT.M34

namespace PoincareMT.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

namespace StandardCapImport

/-- Every actual boundary point is approached from the open core,
using its genuine local defining function (Proposition 9.79(3)). -/
theorem boundary_subset_closure_core : N.boundary_sphere ⊆ closure N.core := by
  rw [N.core_eq_interior_closed_core]
  intro x hx
  obtain ⟨U, f, hU, hxU, _, hsub, hzero, hf, d, _, hd⟩ :=
    N.boundary_local_defining_function x hx
  apply M34.mem_closure_interior_of_local_regular_sublevel hU hxU hsub hzero
    hf.continuousOn ((hf.contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp))
  intro hz
  exact hd (by rw [hz]; rfl)

end StandardCapImport

export StandardCapImport (boundary_subset_closure_core)

namespace StandardCapImport

/-- The recorded compact core is exactly the closure of its recorded
interior; this supplies the regular side of the collar (Proposition 9.79(3)). -/
theorem closure_core_eq_closed_core : closure N.core = N.closed_core := by
  apply Subset.antisymm
  · apply N.closed_core_compact.isClosed.closure_subset_iff.mpr
    rw [N.core_eq_interior_closed_core]
    exact interior_subset
  · intro x hx
    by_cases hi : x ∈ interior N.closed_core
    · exact subset_closure (N.core_eq_interior_closed_core.symm ▸ hi)
    · apply N.boundary_subset_closure_core
      rw [← N.core_frontier_eq_boundary]
      exact ⟨subset_closure hx, hi⟩

end StandardCapImport

export StandardCapImport (closure_core_eq_closed_core)

end PoincareMT.CapCertificate
