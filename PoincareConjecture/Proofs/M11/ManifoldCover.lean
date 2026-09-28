import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] {ι : Type*} {Y : ι → Type*}
  [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace H (Y i)]

def coverChart (e : ∀ i, OpenPartialHomeomorph (Y i) X) (i : ι) (y : Y i) :
    OpenPartialHomeomorph X H :=
  (e i).symm.trans (chartAt H y)

noncomputable abbrev coverChartedSpace (e : ∀ i, OpenPartialHomeomorph (Y i) X)
    (hc : ∀ x : X, ∃ i, x ∈ (e i).target) : ChartedSpace H X where
  atlas := {c | ∃ i y, c = coverChart (H := H) e i y}
  chartAt x := coverChart (H := H) e (Classical.choose (hc x))
    ((e (Classical.choose (hc x))).symm x)
  mem_chart_source x := ⟨Classical.choose_spec (hc x), mem_chart_source H _⟩
  chart_mem_atlas _ := ⟨_, _, rfl⟩

theorem coverChart_transition_smooth [∀ i, IsManifold J ∞ (Y i)]
    (e : ∀ i, OpenPartialHomeomorph (Y i) X)
    (hs : ∀ i j, ContMDiffOn J J ∞ ((e i).trans (e j).symm)
      ((e i).trans (e j).symm).source)
    (i j : ι) (y : Y i) (z : Y j) :
    ContMDiffOn J J ∞ ((coverChart (H := H) e i y).symm.trans
      (coverChart (H := H) e j z))
      ((coverChart (H := H) e i y).symm.trans (coverChart (H := H) e j z)).source := by
  have hy : ContMDiffOn J J ∞ (chartAt H y).symm (chartAt H y).target :=
    contMDiffOn_chart_symm
  have hz : ContMDiffOn J J ∞ (chartAt H z) (chartAt H z).source :=
    contMDiffOn_chart
  apply (hz.comp' ((hs i j).comp' hy)).mono
  dsimp [coverChart]
  mfld_set_tac

theorem cover_isManifold [∀ i, IsManifold J ∞ (Y i)]
    (e : ∀ i, OpenPartialHomeomorph (Y i) X)
    (hc : ∀ x : X, ∃ i, x ∈ (e i).target)
    (hs : ∀ i j, ContMDiffOn J J ∞ ((e i).trans (e j).symm)
      ((e i).trans (e j).symm).source) :
    letI := coverChartedSpace (H := H) e hc
    IsManifold J ∞ X := by
  let := coverChartedSpace (H := H) e hc
  apply isManifold_of_contDiffOn
  rintro c d ⟨i, y, rfl⟩ ⟨j, z, rfl⟩
  rw [← contMDiffOn_iff_contDiffOn]
  apply J.contMDiff.comp_contMDiffOn
  exact (coverChart_transition_smooth e hs i j y z).comp
    (J.contMDiffOn_symm.mono inter_subset_right) inter_subset_left

theorem cover_map_smooth [∀ i, IsManifold J ∞ (Y i)]
    (e : ∀ i, OpenPartialHomeomorph (Y i) X)
    (hc : ∀ x : X, ∃ i, x ∈ (e i).target)
    (hs : ∀ i j, ContMDiffOn J J ∞ ((e i).trans (e j).symm)
      ((e i).trans (e j).symm).source) (i : ι) :
    letI := coverChartedSpace (H := H) e hc
    ContMDiffOn J J ∞ (e i) (e i).source := by
  let := coverChartedSpace (H := H) e hc
  let : IsManifold J ∞ X := cover_isManifold e hc hs
  intro y hy
  let c := coverChart (H := H) e i y
  have hcmax : c ∈ IsManifold.maximalAtlas J ∞ X :=
    IsManifold.subset_maximalAtlas ⟨i, y, rfl⟩
  have htarget : chartAt H y y ∈ c.target := by
    refine ⟨mem_chart_target _ y, ?_⟩
    change (chartAt H y).symm (chartAt H y y) ∈ (e i).source
    rw [(chartAt H y).left_inv (mem_chart_source H y)]
    exact hy
  have hcomp := (contMDiffAt_symm_of_mem_maximalAtlas hcmax htarget).comp y
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas y)
      (mem_chart_source H y))
  apply ContMDiffAt.contMDiffWithinAt
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [chart_source_mem_nhds (H := H) y] with z hz
  change e i z = e i ((chartAt H y).symm (chartAt H y z))
  rw [(chartAt H y).left_inv hz]

theorem cover_inverse_smooth [∀ i, IsManifold J ∞ (Y i)]
    (e : ∀ i, OpenPartialHomeomorph (Y i) X)
    (hc : ∀ x : X, ∃ i, x ∈ (e i).target)
    (hs : ∀ i j, ContMDiffOn J J ∞ ((e i).trans (e j).symm)
      ((e i).trans (e j).symm).source) (i : ι) :
    letI := coverChartedSpace (H := H) e hc
    ContMDiffOn J J ∞ (e i).symm (e i).target := by
  let := coverChartedSpace (H := H) e hc
  let : IsManifold J ∞ X := cover_isManifold e hc hs
  intro x hx
  let y := (e i).symm x
  let c := coverChart (H := H) e i y
  have hcmax : c ∈ IsManifold.maximalAtlas J ∞ X :=
    IsManifold.subset_maximalAtlas ⟨i, y, rfl⟩
  have hsource : x ∈ c.source := ⟨hx, mem_chart_source H y⟩
  have hcomp := (contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := J) y) (mem_chart_target H y)).comp x
    (contMDiffAt_of_mem_maximalAtlas hcmax hsource)
  apply ContMDiffAt.contMDiffWithinAt
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hsource] with z hz
  change (e i).symm z = (chartAt H y).symm (chartAt H y ((e i).symm z))
  have hz' : (e i).symm z ∈ (chartAt H y).source := hz.2
  exact ((chartAt H y).left_inv hz').symm

theorem cover_localDiffeomorph [∀ i, IsManifold J ∞ (Y i)]
    (e : ∀ i, OpenPartialHomeomorph (Y i) X)
    (hc : ∀ x : X, ∃ i, x ∈ (e i).target)
    (hs : ∀ i j, ContMDiffOn J J ∞ ((e i).trans (e j).symm)
      ((e i).trans (e j).symm).source) (i : ι)
    (hsource : (e i).source = univ) :
    letI := coverChartedSpace (H := H) e hc
    IsLocalDiffeomorph J J ∞ (e i) := by
  let := coverChartedSpace (H := H) e hc
  intro y
  refine ⟨{
    toPartialEquiv := (e i).toPartialEquiv
    open_source := (e i).open_source
    open_target := (e i).open_target
    contMDiffOn_toFun := cover_map_smooth e hc hs i
    contMDiffOn_invFun := cover_inverse_smooth e hc hs i
  }, ?_, fun _ _ ↦ rfl⟩
  change y ∈ (e i).source
  rw [hsource]
  trivial

theorem cover_smooth_iff [∀ i, IsManifold J ∞ (Y i)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Type*} [TopologicalSpace K] {L : ModelWithCorners ℝ F K}
    {N : Type*} [TopologicalSpace N] [ChartedSpace K N]
    (e : ∀ i, OpenPartialHomeomorph (Y i) X)
    (hc : ∀ x : X, ∃ i, x ∈ (e i).target)
    (hs : ∀ i j, ContMDiffOn J J ∞ ((e i).trans (e j).symm)
      ((e i).trans (e j).symm).source) (f : X → N) :
    letI := coverChartedSpace (H := H) e hc
    ContMDiff J L ∞ f ↔ ∀ i, ContMDiffOn J L ∞ (f ∘ e i) (e i).source := by
  let := coverChartedSpace (H := H) e hc
  constructor
  · intro hf i
    exact hf.comp_contMDiffOn (cover_map_smooth e hc hs i)
  · intro hf x
    obtain ⟨i, hi⟩ := hc x
    have hy := (e i).map_target hi
    have hlocal := (hf i).contMDiffAt ((e i).open_source.mem_nhds hy)
    have hinverse := (cover_inverse_smooth e hc hs i).contMDiffAt
      ((e i).open_target.mem_nhds hi)
    apply (hlocal.comp x hinverse).congr_of_eventuallyEq
    filter_upwards [(e i).open_target.mem_nhds hi] with z hz
    change f z = f (e i ((e i).symm z))
    rw [(e i).right_inv hz]

end PoincareConjecture.Proofs.M11
