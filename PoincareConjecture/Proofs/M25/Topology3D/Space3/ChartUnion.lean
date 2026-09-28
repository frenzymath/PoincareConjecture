import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

section Topological

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable (e f : OpenPartialHomeomorph X Y)
variable (h : EqOn e f (e.source ∩ f.source))
variable (hi : EqOn e.symm f.symm (e.target ∩ f.target))

noncomputable def glueOpenCharts : OpenPartialHomeomorph X Y := by
  classical
  let F : X → Y := e.source.piecewise e f
  let G : Y → X := e.target.piecewise e.symm f.symm
  have hFe : EqOn F e e.source := by
    intro x hx
    simp only [F, piecewise_eq_of_mem e.source e f hx]
  have hFf : EqOn F f f.source := by
    intro x hx
    by_cases he : x ∈ e.source
    · simpa only [F, piecewise_eq_of_mem e.source e f he] using h ⟨he, hx⟩
    · simp only [F, piecewise_eq_of_notMem e.source e f he]
  have hGe : EqOn G e.symm e.target := by
    intro y hy
    simp only [G, piecewise_eq_of_mem e.target e.symm f.symm hy]
  have hGf : EqOn G f.symm f.target := by
    intro y hy
    by_cases he : y ∈ e.target
    · simpa only [G, piecewise_eq_of_mem e.target e.symm f.symm he] using hi ⟨he, hy⟩
    · simp only [G, piecewise_eq_of_notMem e.target e.symm f.symm he]
  exact {
    toFun := F
    invFun := G
    source := e.source ∪ f.source
    target := e.target ∪ f.target
    map_source' := by
      rintro x (hx | hx)
      · rw [hFe hx]
        exact Or.inl (e.map_source hx)
      · rw [hFf hx]
        exact Or.inr (f.map_source hx)
    map_target' := by
      rintro y (hy | hy)
      · rw [hGe hy]
        exact Or.inl (e.map_target hy)
      · rw [hGf hy]
        exact Or.inr (f.map_target hy)
    left_inv' := by
      rintro x (hx | hx)
      · rw [hFe hx, hGe (e.map_source hx), e.left_inv hx]
      · rw [hFf hx, hGf (f.map_source hx), f.left_inv hx]
    right_inv' := by
      rintro y (hy | hy)
      · rw [hGe hy, hFe (e.map_target hy), e.right_inv hy]
      · rw [hGf hy, hFf (f.map_target hy), f.right_inv hy]
    open_source := e.open_source.union f.open_source
    open_target := e.open_target.union f.open_target
    continuousOn_toFun := (e.continuousOn.congr hFe).union_of_isOpen
      (f.continuousOn.congr hFf) e.open_source f.open_source
    continuousOn_invFun := (e.continuousOn_symm.congr hGe).union_of_isOpen
      (f.continuousOn_symm.congr hGf) e.open_target f.open_target }

@[simp] theorem glueOpenCharts_source :
    (glueOpenCharts e f h hi).source = e.source ∪ f.source := rfl

@[simp] theorem glueOpenCharts_target :
    (glueOpenCharts e f h hi).target = e.target ∪ f.target := rfl

theorem glueOpenCharts_eqOn_left : EqOn (glueOpenCharts e f h hi) e e.source := by
  classical
  intro x hx
  exact piecewise_eq_of_mem e.source e f hx

theorem glueOpenCharts_eqOn_right : EqOn (glueOpenCharts e f h hi) f f.source := by
  classical
  intro x hx
  change e.source.piecewise e f x = f x
  by_cases he : x ∈ e.source
  · rw [piecewise_eq_of_mem e.source e f he]
    exact h ⟨he, hx⟩
  · exact piecewise_eq_of_notMem e.source e f he

theorem glueOpenCharts_symm_eqOn_left :
    EqOn (glueOpenCharts e f h hi).symm e.symm e.target := by
  classical
  intro y hy
  exact piecewise_eq_of_mem e.target e.symm f.symm hy

theorem glueOpenCharts_symm_eqOn_right :
    EqOn (glueOpenCharts e f h hi).symm f.symm f.target := by
  classical
  intro y hy
  change e.target.piecewise e.symm f.symm y = f.symm y
  by_cases he : y ∈ e.target
  · rw [piecewise_eq_of_mem e.target e.symm f.symm he]
    exact hi ⟨he, hy⟩
  · exact piecewise_eq_of_notMem e.target e.symm f.symm he

end Topological

section Smooth

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {n : WithTop ℕ∞} (e f : OpenPartialHomeomorph E F)
variable (h : EqOn e f (e.source ∩ f.source))
variable (hi : EqOn e.symm f.symm (e.target ∩ f.target))

theorem glueOpenCharts_contDiffOn
    (he : ContDiffOn 𝕜 n e e.source) (hf : ContDiffOn 𝕜 n f f.source) :
    ContDiffOn 𝕜 n (glueOpenCharts e f h hi) (e.source ∪ f.source) :=
  (he.congr (glueOpenCharts_eqOn_left e f h hi)).union_of_isOpen
    (hf.congr (glueOpenCharts_eqOn_right e f h hi)) e.open_source f.open_source

theorem glueOpenCharts_symm_contDiffOn
    (he : ContDiffOn 𝕜 n e.symm e.target) (hf : ContDiffOn 𝕜 n f.symm f.target) :
    ContDiffOn 𝕜 n (glueOpenCharts e f h hi).symm (e.target ∪ f.target) :=
  (he.congr (glueOpenCharts_symm_eqOn_left e f h hi)).union_of_isOpen
    (hf.congr (glueOpenCharts_symm_eqOn_right e f h hi)) e.open_target f.open_target

end Smooth

end PoincareConjecture.M25.Topology3D
