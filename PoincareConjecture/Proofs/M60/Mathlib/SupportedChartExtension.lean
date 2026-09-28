import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Topology.Algebra.Support

set_option autoImplicit false

open Set Function Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M60

variable {E F M : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [TopologicalSpace M]

noncomputable def supportedChartExtension (e : OpenPartialHomeomorph M E)
    (V : E → F) : M → F := by
  classical
  exact fun p => if p ∈ e.source then V (e p) else 0

theorem supportedChartExtension_of_mem (e : OpenPartialHomeomorph M E)
    (V : E → F) {p : M} (hp : p ∈ e.source) :
    supportedChartExtension e V p = V (e p) := by
  simp only [supportedChartExtension, if_pos hp]

variable [T2Space M]

theorem tsupport_supportedChartExtension_subset (e : OpenPartialHomeomorph M E)
    {V : E → F} (hV : HasCompactSupport V) (hsource : tsupport V ⊆ e.target) :
    tsupport (supportedChartExtension e V) ⊆ e.symm '' tsupport V := by
  have hclosed : IsClosed (e.symm '' tsupport V) :=
    (hV.image_of_continuousOn (e.continuousOn_symm.mono hsource)).isClosed
  apply closure_minimal _ hclosed
  intro p hp
  have hp' : p ∈ e.source := by
    by_contra h
    exact hp (by simp [supportedChartExtension, h])
  have hVp : e p ∈ tsupport V := subset_tsupport V (by
    simpa only [mem_support, supportedChartExtension_of_mem e V hp'] using hp)
  exact ⟨e p, hVp, e.left_inv hp'⟩

theorem hasCompactSupport_supportedChartExtension (e : OpenPartialHomeomorph M E)
    {V : E → F} (hV : HasCompactSupport V) (hsource : tsupport V ⊆ e.target) :
    HasCompactSupport (supportedChartExtension e V) :=
  (hV.image_of_continuousOn (e.continuousOn_symm.mono hsource)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_supportedChartExtension_subset e hV hsource)

variable {H : Type*} [TopologicalSpace H] [NormedSpace ℝ E] [NormedSpace ℝ F]
  [ChartedSpace H M] {I : ModelWithCorners ℝ E H}

theorem contMDiff_supportedChartExtension (e : OpenPartialHomeomorph M E)
    (he : ContMDiffOn I 𝓘(ℝ, E) ∞ e e.source) {V : E → F}
    (hV : ContDiff ℝ ∞ V) (hcompact : HasCompactSupport V)
    (hsource : tsupport V ⊆ e.target) :
    ContMDiff I 𝓘(ℝ, F) ∞ (supportedChartExtension e V) := by
  intro p
  by_cases hp : p ∈ e.source
  · have he' := (he p hp).contMDiffAt (e.open_source.mem_nhds hp)
    apply (hV.contMDiff.contMDiffAt.comp p he').congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hp] with q hq
    exact supportedChartExtension_of_mem e V hq
  · have hout : p ∉ tsupport (supportedChartExtension e V) := by
      intro h
      obtain ⟨z, hz, rfl⟩ := tsupport_supportedChartExtension_subset e hcompact hsource h
      exact hp (e.map_target (hsource hz))
    apply (contMDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport (supportedChartExtension e V)).isOpen_compl.mem_nhds hout]
      with q hq
    exact image_eq_zero_of_notMem_tsupport hq

end PoincareConjecture.M60
