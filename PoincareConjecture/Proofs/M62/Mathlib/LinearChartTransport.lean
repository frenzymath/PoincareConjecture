import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.LocalInvariantProperties









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

noncomputable section




theorem ContinuousLinearEquiv.exists_compatibleChartedSpace
    {K E F : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F]
    (e : E ≃L[K] F) (M : Type*) [TopologicalSpace M]
    [ChartedSpace E M] {r : ℕ∞ω} [IsManifold 𝓘(K, E) r M] :
    ∃ C : ChartedSpace F M, letI := C
      IsManifold 𝓘(K, F) r M ∧
      ContMDiff 𝓘(K, E) 𝓘(K, F) r (id : M → M) ∧
      ContMDiff 𝓘(K, F) 𝓘(K, E) r (id : M → M) := by
  let f : OpenPartialHomeomorph E F := e.toHomeomorph.toOpenPartialHomeomorph
  have hf : f.source = (Set.univ : Set E) := by simp [f]
  let : ChartedSpace F E := f.singletonChartedSpace hf
  let C : ChartedSpace F M := ChartedSpace.comp F E M
  let : ChartedSpace F M := C
  let G₁ : StructureGroupoid F := contDiffGroupoid r (𝓘(K, F))
  let G₂ : StructureGroupoid E := contDiffGroupoid r (𝓘(K, E))
  have hsingleton : @HasGroupoid F _ E _ (f.singletonChartedSpace hf) G₁ :=
    f.singleton_hasGroupoid hf G₁
  let : @HasGroupoid F _ E _ (f.singletonChartedSpace hf) G₁ := hsingleton
  have hconj : ∀ g ∈ G₂, ChartedSpace.LiftPropOn
      (StructureGroupoid.IsLocalStructomorphWithinAt G₁) (g : E → E) g.source := by
    intro g hg x hx
    rw [ChartedSpace.liftPropWithinAt_iff']
    refine ⟨g.continuousOn.continuousWithinAt hx, ?_⟩
    intro hy
    let q : OpenPartialHomeomorph F F := f.symm.trans (g.trans f)
    have hqmem : q ∈ G₁ := by
      change q ∈ contDiffGroupoid r (𝓘(K, F))
      rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
      have hg' := (show g ∈ contDiffGroupoid r (𝓘(K, E)) from hg)
      rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hg'
      have hgin : ContDiffOn K r (g : E → E) g.source := by
        simpa [contDiffPregroupoid] using hg'.1
      have hginv : ContDiffOn K r (g.symm : E → E) g.symm.source := by
        simpa [contDiffPregroupoid] using hg'.2
      have hqcont : ContDiffOn K r (q : F → F) q.source := by
        simpa [q, f, Function.comp_def] using e.contDiff.comp_contDiffOn
          (hgin.comp_continuousLinearMap (e.symm : F →L[K] E))
      have hqinvcont : ContDiffOn K r (q.symm : F → F) q.symm.source := by
        simpa [q, f, Function.comp_def] using e.contDiff.comp_contDiffOn
          (hginv.comp_continuousLinearMap (e.symm : F →L[K] E))
      exact ⟨by simpa [contDiffPregroupoid] using hqcont,
        by simpa [contDiffPregroupoid] using hqinvcont⟩
    refine ⟨q, hqmem, ?_, ?_⟩
    · intro y hy'
      simp [q, f]
    · simpa [q, f, hf] using hx
  have hcomp : @HasGroupoid F _ M _ C G₁ := by
    let : @HasGroupoid F _ E _ (f.singletonChartedSpace hf) G₁ := hsingleton
    exact StructureGroupoid.HasGroupoid.comp G₂ hconj
  let : @HasGroupoid F _ M _ C G₁ := hcomp
  have hM : IsManifold 𝓘(K, F) r M := IsManifold.mk' (𝓘(K, F)) r M
  let : IsManifold 𝓘(K, F) r M := hM
  refine ⟨C, hM, ?_, ?_⟩
  · rw [contMDiff_iff]
    refine ⟨continuous_id, ?_⟩
    intro x y
    have hxy := (contDiffGroupoid r (𝓘(K, E))).compatible
      (chart_mem_atlas E x) (chart_mem_atlas E y)
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hxy
    have htrans : ContDiffOn K r
        ((chartAt E x).symm.trans (chartAt E y) : E → E)
        ((chartAt E x).symm.trans (chartAt E y)).source := by
      simpa [contDiffPregroupoid] using hxy.1
    rw [extChartAt_comp]
    simpa [extChartAt, f, Function.comp_def] using e.contDiff.comp_contDiffOn htrans
  · rw [contMDiff_iff]
    refine ⟨continuous_id, ?_⟩
    intro x y
    have hxy := (contDiffGroupoid r (𝓘(K, E))).compatible
      (chart_mem_atlas E x) (chart_mem_atlas E y)
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hxy
    have htrans : ContDiffOn K r
        ((chartAt E x).symm.trans (chartAt E y) : E → E)
        ((chartAt E x).symm.trans (chartAt E y)).source := by
      simpa [contDiffPregroupoid] using hxy.1
    rw [extChartAt_comp]
    simpa [extChartAt, f, Function.comp_def, Set.preimage, Set.inter_def] using
      htrans.comp_continuousLinearMap (e.symm : F →L[K] E)
