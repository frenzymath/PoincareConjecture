import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

theorem exists_contDiffOn_limit_of_open_exhaustion
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {Ω : Set E} {U : ι → Set E} (hU : ∀ i, IsOpen (U i))
    (hsub : ∀ i, U i ⊆ Ω) (hcover : ∀ x ∈ Ω, ∃ i, x ∈ U i)
    (hcompact : ∀ K, IsCompact K → K ⊆ Ω → ∃ i, K ⊆ U i)
    {f : ℕ → E → F} {g : ι → E → F}
    (hg : ∀ i, ContDiffOn 𝕜 ∞ (g i) (U i))
    (hconv : ∀ i m K, IsCompact K → K ⊆ U i →
      TendstoUniformlyOn (fun k => iteratedFDeriv 𝕜 m (f k))
        (iteratedFDeriv 𝕜 m (g i)) atTop K) :
    ∃ G : E → F, ContDiffOn 𝕜 ∞ G Ω ∧
      ∀ m K, IsCompact K → K ⊆ Ω →
        TendstoUniformlyOn (fun k => iteratedFDeriv 𝕜 m (f k))
          (iteratedFDeriv 𝕜 m G) atTop K := by
  classical
  have hpoint (i : ι) {x : E} (hx : x ∈ U i) :
      Tendsto (fun k => f k x) atTop (𝓝 (g i x)) := by
    have hev := ContinuousMultilinearMap.uniformContinuous_eval_const
      (𝕜 := 𝕜) (F := F) (0 : Fin 0 → E)
    have h := hev.comp_tendstoUniformlyOn
      (hconv i 0 {x} isCompact_singleton (singleton_subset_iff.mpr hx))
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      h.tendsto_at (mem_singleton x)
  have hcompat (i j : ι) {x : E} (hi : x ∈ U i) (hj : x ∈ U j) : g i x = g j x :=
    tendsto_nhds_unique (hpoint i hi) (hpoint j hj)
  let G : E → F := fun x => if hx : x ∈ Ω then g (hcover x hx).choose x else 0
  have heq (i : ι) : EqOn G (g i) (U i) := by
    intro x hx
    have hxΩ := hsub i hx
    simp only [G, dif_pos hxΩ]
    exact hcompat _ i (hcover x hxΩ).choose_spec hx
  have hgerm (i : ι) {x : E} (hx : x ∈ U i) : G =ᶠ[𝓝 x] g i := by
    filter_upwards [(hU i).mem_nhds hx] with y hy
    exact heq i hy
  refine ⟨G, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    exact (((hg i).contDiffAt ((hU i).mem_nhds hi)).congr_of_eventuallyEq
      (hgerm i hi)).contDiffWithinAt
  · intro m K hK hKΩ
    obtain ⟨i, hKi⟩ := hcompact K hK hKΩ
    apply (hconv i m K hK hKi).congr_right
    intro x hx
    exact ((hgerm i (hKi hx)).iteratedFDeriv (𝕜 := 𝕜) m).eq_of_nhds.symm
