import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv







open _root_.AddCircle

namespace M38Schoenflies










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology AddCommGroup
open scoped Manifold ContDiff

set_option maxHeartbeats 800000 in



theorem AddCircle.exists_flatChartedSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : ℝ ≃L[ℝ] E) {p : ℝ} (hp : 0 < p) :
    ∃ C : ChartedSpace E (AddCircle p), letI := C
      IsManifold 𝓘(ℝ, E) ∞ (AddCircle p) ∧
      IsLocalDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
        (fun s : ℝ => (s : AddCircle p)) ∧
      ∀ s : ℝ, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        (fun r : ℝ => (r : AddCircle p)) s e.toContinuousLinearMap := by
  classical
  let : Fact (0 < p) := ⟨hp⟩
  let O := AddCircle.openPartialHomeomorphCoe p
  let f (a : ℝ) : OpenPartialHomeomorph (AddCircle p) E :=
    (O a).symm.trans e.toHomeomorph.toOpenPartialHomeomorph
  let cut (q : AddCircle p) : ℝ := (AddCircle.equivIco p 0 q : ℝ) - p / 2
  have hsource (q : AddCircle p) : q ∈ (f (cut q)).source := by
    have hr : (AddCircle.equivIco p 0 q : ℝ) ∈ Ioo (cut q) (cut q + p) := by
      dsimp only [cut]
      constructor <;> linarith
    have hq := (O (cut q)).map_source hr
    simpa [f, O] using hq
  let C : ChartedSpace E (AddCircle p) :=
    { atlas := Set.range f
      chartAt := fun q => f (cut q)
      mem_chart_source := hsource
      chart_mem_atlas := fun q => ⟨cut q, rfl⟩ }
  let : ChartedSpace E (AddCircle p) := C
  have hchart (q : AddCircle p) : chartAt E q = f (cut q) := rfl
  have hmod (a x : ℝ) (hx : (x : AddCircle p) ≠ (a : AddCircle p)) :
      ContDiffAt ℝ ∞ (fun r : ℝ => e (AddCircle.equivIco p a (r : AddCircle p))) x ∧
      HasFDerivAt (fun r : ℝ => e (AddCircle.equivIco p a (r : AddCircle p)))
        e.toContinuousLinearMap x := by
    have hk := eventuallyEq_toIcoDiv_nhds hp a
      (not_modEq_iff_ne_mod_zmultiples.mpr hx)
    have heq : (fun r : ℝ => e (AddCircle.equivIco p a (r : AddCircle p))) =ᶠ[𝓝 x]
        (fun r => e (r - toIcoDiv hp a x • p)) := by
      filter_upwards [hk] with r hr
      change e (toIcoMod hp a r) = _
      dsimp only [toIcoMod]
      rw [hr]
    refine ⟨(e.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt.congr_of_eventuallyEq heq,
      ?_⟩
    have hd := e.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const (toIcoDiv hp a x • p))
    simpa only [ContinuousLinearMap.comp_id] using hd.congr_of_eventuallyEq heq
  have hM : IsManifold 𝓘(ℝ, E) ∞ (AddCircle p) := by
    apply isManifold_of_contDiffOn
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩ z hz
    have hz' : ((e.symm z : ℝ) : AddCircle p) ≠ (b : AddCircle p) := by
      simpa [f, O] using hz.1.2
    apply ContDiffAt.contDiffWithinAt
    simpa [f, O, Function.comp_def] using
      (hmod b (e.symm z) hz').1.comp z e.symm.contDiff.contDiffAt
  let : IsManifold 𝓘(ℝ, E) ∞ (AddCircle p) := hM
  have hquotient : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun s : ℝ => (s : AddCircle p)) := by
    intro s
    apply contMDiffAt_iff.mpr
    refine ⟨(AddCircle.continuous_mk' p).continuousAt, ?_⟩
    have hs : (s : AddCircle p) ≠ (cut (s : AddCircle p) : AddCircle p) := by
      simpa [f, O] using hsource (s : AddCircle p)
    simpa [extChartAt, hchart, f, O, Function.comp_def] using
      (hmod (cut (s : AddCircle p)) s hs).1.contDiffWithinAt (s := Set.univ)
  refine ⟨C, hM, ?_, ?_⟩
  · intro s
    let a := s - p / 2
    have hs : s ∈ (O a).source := by
      change s ∈ Ioo (s - p / 2) (s - p / 2 + p)
      constructor <;> linarith
    have hf : f a ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ (AddCircle p) :=
      IsManifold.subset_maximalAtlas ⟨a, rfl⟩
    have hinv : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (O a).symm (O a).target := by
      have hi := e.symm.contDiff.contMDiff.comp_contMDiffOn
        (contMDiffOn_of_mem_maximalAtlas hf)
      change ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
        (fun q : AddCircle p => (AddCircle.equivIco p a q : ℝ)) {(a : AddCircle p)}ᶜ
      simpa [f, O, Function.comp_def] using hi
    let Φ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ℝ (AddCircle p) ∞ :=
      { toPartialEquiv := (O a).toPartialEquiv
        open_source := (O a).open_source
        open_target := (O a).open_target
        contMDiffOn_toFun := hquotient.contMDiffOn
        contMDiffOn_invFun := hinv }
    exact ⟨Φ, hs, fun _ _ => rfl⟩
  · intro s
    refine ⟨(AddCircle.continuous_mk' p).continuousAt, ?_⟩
    have hs : (s : AddCircle p) ≠ (cut (s : AddCircle p) : AddCircle p) := by
      simpa [f, O] using hsource (s : AddCircle p)
    simpa [writtenInExtChartAt, extChartAt, hchart, f, O, Function.comp_def] using
      (hmod (cut (s : AddCircle p)) s hs).2.hasFDerivWithinAt (s := Set.univ)

end M38Schoenflies
