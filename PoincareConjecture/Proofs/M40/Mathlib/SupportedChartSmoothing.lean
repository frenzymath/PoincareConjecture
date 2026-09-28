import PoincareConjecture.Proofs.M40.Mathlib.ChartPerturbation
import PoincareConjecture.Proofs.M40.Mathlib.LipschitzSmoothingBlend
import Mathlib.Geometry.Manifold.Algebra.SMul












set_option autoImplicit false

open Set Function Filter
open scoped Topology Manifold ContDiff NNReal

namespace PoincareConjecture.M40

section Topological

variable {E F M N : Type*}
  [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



def chartSmoothingDisplacement (e : OpenPartialHomeomorph M E)
    (h : OpenPartialHomeomorph N F) (ρ : M → ℝ) (f : M → N) (G : E → F) :
    M → F := fun x => ρ x • (G (e x) - h (f x))



theorem tsupport_chartSmoothingDisplacement_subset
    (e : OpenPartialHomeomorph M E) (h : OpenPartialHomeomorph N F)
    (ρ : M → ℝ) (f : M → N) (G : E → F) :
    tsupport (chartSmoothingDisplacement e h ρ f G) ⊆ tsupport ρ :=
  tsupport_smul_subset_left _ _



noncomputable def supportedChartSmoothing (e : OpenPartialHomeomorph M E)
    (h : OpenPartialHomeomorph N F) (U : Set M) (ρ : M → ℝ)
    (f : M → N) (G : E → F) : M → N :=
  chartPerturb h U f (chartSmoothingDisplacement e h ρ f G)



theorem supportedChartSmoothing_of_mem
    (e : OpenPartialHomeomorph M E) (h : OpenPartialHomeomorph N F)
    (U : Set M) (ρ : M → ℝ) (f : M → N) (G : E → F)
    {x : M} (hx : x ∈ U) :
    supportedChartSmoothing e h U ρ f G x =
      h.symm (cutoffBlend ρ (h ∘ f) (G ∘ e) x) := by
  rw [supportedChartSmoothing, chartPerturb_of_mem h U f _ hx]
  congr 1
  dsimp [chartSmoothingDisplacement, cutoffBlend]
  module



theorem supportedChartSmoothing_eventuallyEq
    (e : OpenPartialHomeomorph M E) (h : OpenPartialHomeomorph N F)
    (U : Set M) (ρ : M → ℝ) (f : M → N) (G : E → F)
    (hfU : MapsTo f U h.source) {x : M} (hx : x ∉ tsupport ρ) :
    supportedChartSmoothing e h U ρ f G =ᶠ[𝓝 x] f :=
  chartPerturb_eventuallyEq h U f _ hfU
    (fun hs => hx (tsupport_chartSmoothingDisplacement_subset e h ρ f G hs))



theorem continuous_chartSmoothingDisplacement
    (e : OpenPartialHomeomorph M E) (h : OpenPartialHomeomorph N F)
    {U : Set M} (hU : IsOpen U) (hUe : U ⊆ e.source)
    {ρ : M → ℝ} {f : M → N} {G : E → F}
    (hρ : Continuous ρ) (hf : Continuous f) (hG : Continuous G)
    (hsupp : tsupport ρ ⊆ U) (hfU : MapsTo f U h.source) :
    Continuous (chartSmoothingDisplacement e h ρ f G) := by
  have hc : ContinuousOn (chartSmoothingDisplacement e h ρ f G) U := by
    intro x hx
    exact (hρ.continuousAt.smul
      ((hG.continuousAt.comp (e.continuousAt (hUe hx))).sub
        ((h.continuousAt (hfU hx)).comp hf.continuousAt))).continuousWithinAt
  exact hc.continuous_of_tsupport_subset hU
    ((tsupport_chartSmoothingDisplacement_subset e h ρ f G).trans hsupp)



theorem continuous_supportedChartSmoothing
    (e : OpenPartialHomeomorph M E) (h : OpenPartialHomeomorph N F)
    {U : Set M} (hU : IsOpen U) (hUe : U ⊆ e.source)
    {ρ : M → ℝ} {f : M → N} {G : E → F}
    (hρ : Continuous ρ) (hf : Continuous f) (hG : Continuous G)
    (hsupp : tsupport ρ ⊆ U) (hfU : MapsTo f U h.source)
    (hrange : ∀ x ∈ U,
      h (f x) + chartSmoothingDisplacement e h ρ f G x ∈ h.target) :
    Continuous (supportedChartSmoothing e h U ρ f G) :=
  continuous_chartPerturb h hU hf
    (continuous_chartSmoothingDisplacement e h hU hUe hρ hf hG hsupp hfU)
    ((tsupport_chartSmoothingDisplacement_subset e h ρ f G).trans hsupp) hfU hrange



noncomputable def supportedChartSmoothingHomotopy
    (e : OpenPartialHomeomorph M E) (h : OpenPartialHomeomorph N F)
    {U : Set M} (hU : IsOpen U) (hUe : U ⊆ e.source)
    (ρ : M → ℝ) (f : C(M, N)) (G : E → F)
    (hρ : Continuous ρ) (hG : Continuous G)
    (hsupp : tsupport ρ ⊆ U) (hfU : MapsTo f U h.source)
    (hrange : ∀ (t : unitInterval) (x : M), x ∈ U →
      h (f x) + (t : ℝ) • chartSmoothingDisplacement e h ρ f G x ∈ h.target) :
    f.Homotopy ⟨supportedChartSmoothing e h U ρ f G,
      continuous_supportedChartSmoothing e h hU hUe hρ f.continuous hG
        hsupp hfU (fun x hx => by simpa using hrange 1 x hx)⟩ :=
  chartPerturbHomotopy h hU f (chartSmoothingDisplacement e h ρ f G)
    (continuous_chartSmoothingDisplacement e h hU hUe hρ f.continuous hG hsupp hfU)
    ((tsupport_chartSmoothingDisplacement_subset e h ρ f G).trans hsupp) hfU hrange

end Topological

section Smooth

variable {E H F K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}



theorem contMDiffAt_supportedChartSmoothing_of_contMDiffAt
    (e : OpenPartialHomeomorph M E) (h : OpenPartialHomeomorph N F)
    {U : Set M} (hU : IsOpen U) (hUe : U ⊆ e.source)
    {ρ : M → ℝ} {f : M → N} {G : E → F}
    (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (hG : ContDiff ℝ ∞ G)
    (he : ContMDiffOn I 𝓘(ℝ, E) ∞ e e.source)
    (hh : ContMDiffOn J 𝓘(ℝ, F) ∞ h h.source)
    (hh' : ContMDiffOn 𝓘(ℝ, F) J ∞ h.symm h.target)
    (hsupp : tsupport ρ ⊆ U) (hfU : MapsTo f U h.source)
    (hrange : ∀ x ∈ U,
      h (f x) + chartSmoothingDisplacement e h ρ f G x ∈ h.target)
    {x : M} (hf : ContMDiffAt I J ∞ f x) :
    ContMDiffAt I J ∞ (supportedChartSmoothing e h U ρ f G) x := by
  by_cases hx : x ∈ U
  · have he' := (he x (hUe hx)).contMDiffAt (e.open_source.mem_nhds (hUe hx))
    have hhf := ((hh (f x) (hfU hx)).contMDiffAt
      (h.open_source.mem_nhds (hfU hx))).comp x hf
    have hGe := hG.contMDiff.contMDiffAt.comp x he'
    exact contMDiffAt_chartPerturb_of_mem h hU hx
      (hhf.add ((hρ x).smul (hGe.sub hhf))) hh' (hrange x hx)
  · exact hf.congr_of_eventuallyEq
      (supportedChartSmoothing_eventuallyEq e h U ρ f G hfU (fun hs => hx (hsupp hs)))



theorem contMDiffAt_supportedChartSmoothing_of_eventuallyEq_one
    (e : OpenPartialHomeomorph M E) (h : OpenPartialHomeomorph N F)
    {U : Set M} (hU : IsOpen U) (hUe : U ⊆ e.source)
    {ρ : M → ℝ} {f : M → N} {G : E → F}
    (hG : ContDiff ℝ ∞ G) (he : ContMDiffOn I 𝓘(ℝ, E) ∞ e e.source)
    (hh' : ContMDiffOn 𝓘(ℝ, F) J ∞ h.symm h.target)
    (hsupp : tsupport ρ ⊆ U)
    (hrange : ∀ x ∈ U,
      h (f x) + chartSmoothingDisplacement e h ρ f G x ∈ h.target)
    {x : M} (hρx : ρ =ᶠ[𝓝 x] 1) :
    ContMDiffAt I J ∞ (supportedChartSmoothing e h U ρ f G) x := by
  have hρone : ρ x = 1 := hρx.self_of_nhds
  have hx : x ∈ U := hsupp (subset_tsupport ρ (by simp [mem_support, hρone]))
  have he' := (he x (hUe hx)).contMDiffAt (e.open_source.mem_nhds (hUe hx))
  apply contMDiffAt_chartPerturb_of_mem h hU hx ?_ hh' (hrange x hx)
  apply (hG.contMDiff.contMDiffAt.comp x he').congr_of_eventuallyEq
  filter_upwards [hρx] with y hy
  simp only [chartSmoothingDisplacement, hy, Pi.one_apply, one_smul]
  abel

end Smooth

section Distance

variable {E F M N : Type*}
  [TopologicalSpace M] [PseudoMetricSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem dist_supportedChartSmoothing_le
    (e : OpenPartialHomeomorph M E) (h : OpenPartialHomeomorph N F)
    (U : Set M) (ρ : M → ℝ) (f : M → N) (G : E → F)
    (hfU : MapsTo f U h.source) {V : Set F} {C : ℝ≥0}
    (hLip : LipschitzOnWith C h.symm V)
    {x : M} (hx : x ∈ U) (hρx : ρ x ∈ Icc 0 1)
    (hV : h (f x) ∈ V) (hV' : cutoffBlend ρ (h ∘ f) (G ∘ e) x ∈ V) :
    dist (supportedChartSmoothing e h U ρ f G x) (f x) ≤
      (C : ℝ) * dist (G (e x)) (h (f x)) := by
  have hdist : dist (cutoffBlend ρ (h ∘ f) (G ∘ e) x) (h (f x)) ≤
      dist (G (e x)) (h (f x)) := by
    have heq : cutoffBlend ρ (h ∘ f) (G ∘ e) x - h (f x) =
        ρ x • (G (e x) - h (f x)) := by
      dsimp [cutoffBlend]
      module
    rw [dist_eq_norm, heq, norm_smul, Real.norm_of_nonneg hρx.1, dist_eq_norm]
    exact mul_le_of_le_one_left (norm_nonneg _) hρx.2
  rw [supportedChartSmoothing_of_mem e h U ρ f G hx]
  calc
    dist (h.symm (cutoffBlend ρ (h ∘ f) (G ∘ e) x)) (f x) =
        dist (h.symm (cutoffBlend ρ (h ∘ f) (G ∘ e) x)) (h.symm (h (f x))) := by
          rw [h.left_inv (hfU hx)]
    _ ≤ (C : ℝ) * dist (cutoffBlend ρ (h ∘ f) (G ∘ e) x) (h (f x)) :=
      hLip.dist_le_mul _ hV' _ hV
    _ ≤ (C : ℝ) * dist (G (e x)) (h (f x)) :=
      mul_le_mul_of_nonneg_left hdist C.coe_nonneg

end Distance

end PoincareConjecture.M40
