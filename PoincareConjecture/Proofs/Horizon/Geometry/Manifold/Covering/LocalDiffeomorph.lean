import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

noncomputable section

namespace Poincare.Manifold.LocalHomeomorphLift

variable {H X M : Type*} [TopologicalSpace H] [TopologicalSpace X]
  [TopologicalSpace M] [ChartedSpace H M]
  {f : X → M} (hf : IsLocalHomeomorph f)

def localChart (x : X) : OpenPartialHomeomorph X H :=
  (hf.localInverseAt x).symm.trans (chartAt H (f x))

@[reducible] def chartedSpace : ChartedSpace H X where
  atlas := range (localChart (H := H) hf)
  chartAt := localChart hf
  mem_chart_source x := by simp [localChart]
  chart_mem_atlas x := ⟨x, rfl⟩

theorem localChart_apply (x y : X) : localChart (H := H) hf x y = chartAt H (f x) (f y) := by
  simp [localChart]

theorem projection_localChart_symm (x : X) {z : H}
    (hz : z ∈ (localChart (H := H) hf x).target) :
    f ((localChart (H := H) hf x).symm z) = (chartAt H (f x)).symm z := by
  apply hf.apply_localInverseAt_of_mem
  exact hz.2

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (r : ℕ∞ω)

private theorem contDiffOn_model (a : H) {g : H → H} {s : Set H}
    (hg : ContMDiffOn I I r g s) :
    ContDiffOn 𝕜 r (I ∘ g ∘ I.symm) (I.symm ⁻¹' s ∩ range I) := by
  have hs : s ⊆ (extChartAt I a).source := by simp
  have ht : MapsTo g s (extChartAt I a).source := by simp
  have h := (contMDiffOn_iff_of_subset_source' hs ht).mp hg
  have hset : extChartAt I a '' s = I.symm ⁻¹' s ∩ range I := by
    rw [← I.image_eq]
    apply Set.image_congr'
    intro z
    simp only [extChartAt_coe, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
      Function.comp_apply, id_eq]
  rw [hset] at h
  refine h.congr (fun z _ => ?_)
  simp only [Function.comp_apply, extChartAt_coe, extChartAt_coe_symm, chartAt_self_eq,
    OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id_eq]

theorem isManifold [IsManifold I r M] :
    letI := chartedSpace (H := H) hf
    IsManifold I r X := by
  let := chartedSpace (H := H) hf
  apply isManifold_of_contDiffOn I r X
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
  apply contDiffOn_model I r (chartAt H (f x) (f x))
  have hbase : ContMDiffOn I I r
      ((chartAt H (f x)).symm.trans (chartAt H (f y)))
      ((chartAt H (f x)).symm.trans (chartAt H (f y))).source :=
    (contMDiffOn_chart (I := I) (x := f y)).comp'
      (contMDiffOn_chart_symm (I := I) (x := f x))
  have hsub : ((localChart (H := H) hf x).symm.trans (localChart (H := H) hf y)).source ⊆
      ((chartAt H (f x)).symm.trans (chartAt H (f y))).source := by
    intro z hz
    refine ⟨hz.1.1, ?_⟩
    have h := hz.2.2
    change (hf.localInverseAt y).symm ((localChart hf x).symm z) ∈
      (chartAt H (f y)).source at h
    simp only [hf.localInverseAt_symm, projection_localChart_symm hf x hz.1] at h
    exact h
  apply (hbase.mono hsub).congr
  intro z hz
  change (localChart hf y) ((localChart hf x).symm z) =
    chartAt H (f y) ((chartAt H (f x)).symm z)
  rw [localChart_apply, projection_localChart_symm hf x hz.1]


theorem isLocalDiffeomorph [IsManifold I r M] :
    letI := chartedSpace (H := H) hf
    IsLocalDiffeomorph I I r f := by
  let := chartedSpace (H := H) hf
  let := isManifold hf I r
  intro x
  have hx : localChart (H := H) hf x ∈ IsManifold.maximalAtlas I r X :=
    IsManifold.subset_maximalAtlas ⟨x, rfl⟩
  have hy : chartAt H (f x) ∈ IsManifold.maximalAtlas I r M :=
    IsManifold.chart_mem_maximalAtlas (f x)
  let dx : PartialDiffeomorph I I X H r :=
    { toPartialEquiv := (localChart hf x).toPartialEquiv
      open_source := (localChart hf x).open_source
      open_target := (localChart hf x).open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hx
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hx }
  let dy : PartialDiffeomorph I I M H r :=
    { toPartialEquiv := (chartAt H (f x)).toPartialEquiv
      open_source := (chartAt H (f x)).open_source
      open_target := (chartAt H (f x)).open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hy
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hy }
  refine ⟨dx.trans dy.symm, ?_, ?_⟩
  · change x ∈ (localChart hf x).source ∧
      localChart hf x x ∈ (chartAt H (f x)).target
    constructor
    · exact mem_chart_source H x
    · rw [localChart_apply]
      exact (chartAt H (f x)).map_source (mem_chart_source H (f x))
  · intro y hy
    change f y = (chartAt H (f x)).symm (localChart hf x y)
    rw [localChart_apply]
    apply ((chartAt H (f x)).left_inv _).symm
    have h := hy.1.2
    change (hf.localInverseAt x).symm y ∈ (chartAt H (f x)).source at h
    simpa only [hf.localInverseAt_symm] using h


theorem contMDiff_of_continuous_projection [IsManifold I r M] {g : X → X}
    (hg : Continuous g) :
    letI := chartedSpace (H := H) hf
    ContMDiff I I r (f ∘ g) → ContMDiff I I r g := by
  let := chartedSpace (H := H) hf
  let := isManifold hf I r
  intro hfg x
  let hx := isLocalDiffeomorph hf I r (g x)
  have hs := hx.localInverse_contMDiffAt.comp x (hfg x)
  apply hs.congr_of_eventuallyEq
  filter_upwards [hg.continuousAt.preimage_mem_nhds
    (hx.localInverse.open_target.mem_nhds hx.localInverse_mem_target)] with y hy
  exact (hx.localInverse_left_inv hy).symm

end Poincare.Manifold.LocalHomeomorphLift
