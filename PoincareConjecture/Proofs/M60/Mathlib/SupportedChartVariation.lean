import PoincareConjecture.Proofs.M40.Mathlib.ChartPerturbation
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Topology.Compactness.Compact










set_option autoImplicit false

open Set Function Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M60

variable {F M N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [TopologicalSpace N]



noncomputable def supportedChartVariation (e : OpenPartialHomeomorph N F)
    (U : Set M) (f : M → N) (V : M → F) : ℝ × M → N :=
  M40.chartPerturb e (Prod.snd ⁻¹' U) (f ∘ Prod.snd) (fun p => p.1 • V p.2)



theorem supportedChartVariation_zero (e : OpenPartialHomeomorph N F)
    (U : Set M) (f : M → N) (V : M → F) (hfU : MapsTo f U e.source) (p : M) :
    supportedChartVariation e U f V (0, p) = f p :=
  M40.chartPerturb_eq_of_zero e (Prod.snd ⁻¹' U) (f ∘ Prod.snd)
    (fun q : ℝ × M => q.1 • V q.2) (fun _ hp => hfU hp) (by simp)



theorem supportedChartVariation_of_mem (e : OpenPartialHomeomorph N F)
    (U : Set M) (f : M → N) (V : M → F) (s : ℝ) {p : M} (hp : p ∈ U) :
    supportedChartVariation e U f V (s, p) = e.symm (e (f p) + s • V p) :=
  M40.chartPerturb_of_mem e _ _ _ hp



theorem exists_supportedChartVariation_interval (e : OpenPartialHomeomorph N F)
    {U : Set M} (hU : IsOpen U) {f : M → N} {V : M → F}
    (hf : ContinuousOn f U) (hV : Continuous V) (hcompact : HasCompactSupport V)
    (hsupport : tsupport V ⊆ U) (hfU : MapsTo f U e.source) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Ioo (-ε) ε, ∀ p ∈ U, e (f p) + s • V p ∈ e.target := by
  have hnear : ∀ᶠ s : ℝ in 𝓝 0, ∀ p ∈ tsupport V, e (f p) + s • V p ∈ e.target := by
    apply hcompact.eventually_forall_of_forall_eventually
    intro p hp
    have hf' : ContinuousAt f p := hf.continuousAt (hU.mem_nhds (hsupport hp))
    have hfp : ContinuousAt (fun q : ℝ × M => f q.2) (0, p) := hf'.comp continuousAt_snd
    have hcoord : ContinuousAt (fun q : ℝ × M => e (f q.2)) (0, p) :=
      (e.continuousAt (hfU (hsupport hp))).comp (f := fun q : ℝ × M => f q.2) hfp
    have hc : ContinuousAt (fun q : ℝ × M => e (f q.2) + q.1 • V q.2) (0, p) :=
      hcoord.add
        (continuousAt_fst.smul (hV.continuousAt.comp continuousAt_snd))
    exact hc.preimage_mem_nhds (e.open_target.mem_nhds
      (by simpa using e.map_source (hfU (hsupport hp))))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨ε, hε, ?_⟩
  intro s hs p hp
  by_cases hVp : p ∈ tsupport V
  · apply hball (by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hs) p hVp
  · simpa only [image_eq_zero_of_notMem_tsupport hVp, smul_zero, add_zero] using
      e.map_source (hfU hp)

variable {E H K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace K] [ChartedSpace H M] [ChartedSpace K N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}




theorem contMDiffOn_supportedChartVariation (e : OpenPartialHomeomorph N F)
    {U : Set M} (hU : IsOpen U) {f : M → N} {V : M → F}
    (hf : ContMDiff I J ∞ f) (hV : ContMDiff I 𝓘(ℝ, F) ∞ V)
    (he : ContMDiffOn J 𝓘(ℝ, F) ∞ e e.source)
    (he' : ContMDiffOn 𝓘(ℝ, F) J ∞ e.symm e.target)
    (hsupport : tsupport V ⊆ U) (hfU : MapsTo f U e.source)
    {ε : ℝ} (hrange : ∀ s ∈ Ioo (-ε) ε, ∀ p ∈ U, e (f p) + s • V p ∈ e.target) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) J ∞ (supportedChartVariation e U f V)
      (Ioo (-ε) ε ×ˢ (univ : Set M)) := by
  have hsnd : ContMDiff ((𝓘(ℝ, ℝ)).prod I) I ∞ (Prod.snd : ℝ × M → M) := contMDiff_snd
  have hfst : ContMDiff ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞ (Prod.fst : ℝ × M → ℝ) := contMDiff_fst
  have hbase : ContMDiff ((𝓘(ℝ, ℝ)).prod I) J ∞ (f ∘ Prod.snd) := hf.comp hsnd
  have hdelta : ContMDiff ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, F) ∞
      (fun p : ℝ × M => p.1 • V p.2) := hfst.smul (hV.comp hsnd)
  have hsupp : tsupport (fun p : ℝ × M => p.1 • V p.2) ⊆ Prod.snd ⁻¹' U :=
    (tsupport_smul_subset_right (f := fun p : ℝ × M => p.1) (g := fun p => V p.2)).trans
      ((tsupport_comp_subset_preimage V continuous_snd).trans (preimage_mono hsupport))
  intro p hp
  by_cases hpU : p.2 ∈ U
  · have hc := ((he (f p.2) (hfU hpU)).contMDiffAt
      (e.open_source.mem_nhds (hfU hpU))).comp p (hbase p)
    exact (M40.contMDiffAt_chartPerturb_of_mem e (hU.preimage continuous_snd) hpU
      (hc.add (hdelta p)) he' (hrange p.1 hp.1 p.2 hpU)).contMDiffWithinAt
  · exact ((hbase p).congr_of_eventuallyEq (M40.chartPerturb_eventuallyEq e
      (Prod.snd ⁻¹' U) (f ∘ Prod.snd) (fun p : ℝ × M => p.1 • V p.2)
      (fun _ hq => hfU hq) (fun h => hpU (hsupp h)))).contMDiffWithinAt

end PoincareConjecture.M60
