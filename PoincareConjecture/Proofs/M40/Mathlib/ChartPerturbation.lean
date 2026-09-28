import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic.Abel











set_option autoImplicit false

open Set Function Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M40

section Continuous

variable {M N F : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



noncomputable def chartPerturb (e : OpenPartialHomeomorph N F) (U : Set M)
    (f : M → N) (δ : M → F) : M → N := by
  classical
  exact fun x => if x ∈ U then e.symm (e (f x) + δ x) else f x



theorem chartPerturb_of_mem (e : OpenPartialHomeomorph N F) (U : Set M)
    (f : M → N) (δ : M → F) {x : M} (hx : x ∈ U) :
    chartPerturb e U f δ x = e.symm (e (f x) + δ x) := by
  simp [chartPerturb, hx]



theorem chartPerturb_eq_of_zero (e : OpenPartialHomeomorph N F) (U : Set M)
    (f : M → N) (δ : M → F) (hfU : MapsTo f U e.source)
    {x : M} (hδ : δ x = 0) : chartPerturb e U f δ x = f x := by
  classical
  by_cases hx : x ∈ U
  · rw [chartPerturb_of_mem e U f δ hx, hδ, add_zero, e.left_inv (hfU hx)]
  · simp [chartPerturb, hx]



theorem chartPerturb_eventuallyEq (e : OpenPartialHomeomorph N F) (U : Set M)
    (f : M → N) (δ : M → F) (hfU : MapsTo f U e.source)
    {x : M} (hx : x ∉ tsupport δ) : chartPerturb e U f δ =ᶠ[𝓝 x] f := by
  filter_upwards [(isClosed_tsupport δ).isOpen_compl.mem_nhds hx] with y hy
  exact chartPerturb_eq_of_zero e U f δ hfU (image_eq_zero_of_notMem_tsupport hy)



theorem continuous_chartPerturb (e : OpenPartialHomeomorph N F) {U : Set M}
    (hU : IsOpen U) {f : M → N} {δ : M → F}
    (hf : Continuous f) (hδ : Continuous δ) (hsupp : tsupport δ ⊆ U)
    (hfU : MapsTo f U e.source)
    (hrange : ∀ x ∈ U, e (f x) + δ x ∈ e.target) :
    Continuous (chartPerturb e U f δ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ U
  · have hcoord := ((e.continuousAt (hfU hx)).comp hf.continuousAt).add
      hδ.continuousAt
    have hinv : ContinuousAt e.symm (e (f x) + δ x) :=
      e.continuousAt_symm (hrange x hx)
    have hcomp : ContinuousAt (fun y => e.symm (e (f y) + δ y)) x :=
      hinv.comp (f := fun y => e (f y) + δ y) hcoord
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx] with y hy
    exact chartPerturb_of_mem e U f δ hy
  · exact hf.continuousAt.congr_of_eventuallyEq
      (chartPerturb_eventuallyEq e U f δ hfU (fun h => hx (hsupp h)))



noncomputable def chartPerturbHomotopy
    (e : OpenPartialHomeomorph N F) {U : Set M} (hU : IsOpen U)
    (f : C(M, N)) (δ : M → F) (hδ : Continuous δ) (hsupp : tsupport δ ⊆ U)
    (hfU : MapsTo f U e.source)
    (hrange : ∀ (t : unitInterval) (x : M), x ∈ U →
      e (f x) + (t : ℝ) • δ x ∈ e.target) :
    f.Homotopy ⟨chartPerturb e U f δ,
      continuous_chartPerturb e hU f.continuous hδ hsupp hfU
        (fun x hx => by simpa using hrange 1 x hx)⟩ where
  toFun p := chartPerturb e U f (fun x => (p.1 : ℝ) • δ x) p.2
  continuous_toFun := by
    have hsupport : tsupport (fun p : unitInterval × M => (p.1 : ℝ) • δ p.2) ⊆
        Prod.snd ⁻¹' U :=
      (tsupport_smul_subset_right
        (f := fun p : unitInterval × M => (p.1 : ℝ)) (g := fun p => δ p.2)).trans
        ((tsupport_comp_subset_preimage δ continuous_snd).trans (preimage_mono hsupp))
    exact continuous_chartPerturb e (hU.preimage continuous_snd)
      (f.continuous.comp continuous_snd)
      ((continuous_subtype_val.comp continuous_fst).smul (hδ.comp continuous_snd))
      hsupport (fun p hp => hfU hp) (fun p hp => hrange p.1 p.2 hp)
  map_zero_left x := chartPerturb_eq_of_zero e U f _ hfU (by simp)
  map_one_left x := by
    change chartPerturb e U f (fun y => (1 : ℝ) • δ y) x = chartPerturb e U f δ x
    simp only [one_smul]



theorem chartPerturb_eq_target (e : OpenPartialHomeomorph N F) (U : Set M)
    (f : M → N) (δ : M → F) {b : M} (hb : b ∈ U) {y : N}
    (hy : y ∈ e.source) (hδ : δ b = e y - e (f b)) :
    chartPerturb e U f δ b = y := by
  rw [chartPerturb_of_mem e U f δ hb, hδ]
  have hsum : e (f b) + (e y - e (f b)) = e y := by abel
  rw [hsum, e.left_inv hy]

end Continuous

section Smooth

variable {E H F K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}




theorem contMDiffAt_chartPerturb_of_mem
    (e : OpenPartialHomeomorph N F) {U : Set M} (hU : IsOpen U)
    {f : M → N} {δ : M → F} {x : M} (hx : x ∈ U)
    (hcoord : ContMDiffAt I 𝓘(ℝ, F) ∞ (fun y => e (f y) + δ y) x)
    (he : ContMDiffOn 𝓘(ℝ, F) J ∞ e.symm e.target)
    (hrange : e (f x) + δ x ∈ e.target) :
    ContMDiffAt I J ∞ (chartPerturb e U f δ) x := by
  have hi_at := (he _ hrange).contMDiffAt (e.open_target.mem_nhds hrange)
  apply (hi_at.comp x hcoord).congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact chartPerturb_of_mem e U f δ hy



theorem contMDiff_chartPerturb (e : OpenPartialHomeomorph N F) {U : Set M}
    (hU : IsOpen U) {f : M → N} {δ : M → F}
    (hf : ContMDiff I J ∞ f) (hδ : ContMDiff I 𝓘(ℝ, F) ∞ δ)
    (he : ContMDiffOn J 𝓘(ℝ, F) ∞ e e.source)
    (he' : ContMDiffOn 𝓘(ℝ, F) J ∞ e.symm e.target)
    (hsupp : tsupport δ ⊆ U) (hfU : MapsTo f U e.source)
    (hrange : ∀ x ∈ U, e (f x) + δ x ∈ e.target) :
    ContMDiff I J ∞ (chartPerturb e U f δ) := by
  intro x
  by_cases hx : x ∈ U
  · have he_at := (he _ (hfU hx)).contMDiffAt (e.open_source.mem_nhds (hfU hx))
    exact contMDiffAt_chartPerturb_of_mem e hU hx
      ((he_at.comp x (hf x)).add (hδ x)) he' (hrange x hx)
  · exact (hf x).congr_of_eventuallyEq
      (chartPerturb_eventuallyEq e U f δ hfU (fun h => hx (hsupp h)))

end Smooth

end PoincareConjecture.M40
