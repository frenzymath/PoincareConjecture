import PoincareConjecture.Proofs.M44.Mathlib.UniformCompactJets
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.LinearPrecompose










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

universe u




structure CompactSmoothConvergenceOn
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (fseq : ι → E → F) (f : E → F) (l : Filter ι) (U : Set E) : Prop where
  isOpen : IsOpen U
  smooth : ContDiffOn ℝ ∞ f U
  eventually_smooth : ∀ K : Set E, IsCompact K → K ⊆ U →
    ∀ᶠ i in l, ∀ x ∈ K, ContDiffAt ℝ ∞ (fseq i) x
  jets : ∀ (j : ℕ) (K : Set E), IsCompact K → K ⊆ U →
    TendstoUniformlyOn (fun i => iteratedFDeriv ℝ j (fseq i)) (iteratedFDeriv ℝ j f) l K

namespace CompactSmoothConvergenceOn

variable {E F G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {l : Filter ι} {U : Set E} {fseq : ι → E → F} {f : E → F}


theorem uniformlyOn (h : CompactSmoothConvergenceOn fseq f l U)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) : TendstoUniformlyOn fseq f l K :=
  tendstoUniformlyOn_of_iteratedFDeriv_zero (h.jets 0 K hK hKU)


theorem mono (h : CompactSmoothConvergenceOn fseq f l U)
    {V : Set E} (hV : IsOpen V) (hVU : V ⊆ U) :
    CompactSmoothConvergenceOn fseq f l V where
  isOpen := hV
  smooth := h.smooth.mono hVU
  eventually_smooth K hK hKV := h.eventually_smooth K hK (hKV.trans hVU)
  jets j K hK hKV := h.jets j K hK (hKV.trans hVU)



theorem congr (h : CompactSmoothConvergenceOn fseq f l U)
    {gseq : ι → E → F} {g : E → F}
    (hseq : ∀ i, EqOn (gseq i) (fseq i) U) (hmodel : EqOn g f U) :
    CompactSmoothConvergenceOn gseq g l U where
  isOpen := h.isOpen
  smooth := h.smooth.congr hmodel
  eventually_smooth K hK hKU := by
    filter_upwards [h.eventually_smooth K hK hKU] with i hi
    intro x hx
    exact (hi x hx).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (h.isOpen.mem_nhds (hKU hx)) (hseq i))
  jets j K hK hKU := by
    apply ((h.jets j K hK hKU).congr ?_).congr_right ?_
    · refine Eventually.of_forall fun i x hx => ?_
      have heq := Filter.eventuallyEq_of_mem (h.isOpen.mem_nhds (hKU hx)) (hseq i)
      exact (heq.iteratedFDeriv ℝ j).self_of_nhds.symm
    · intro x hx
      have heq := Filter.eventuallyEq_of_mem (h.isOpen.mem_nhds (hKU hx)) hmodel
      exact (heq.iteratedFDeriv ℝ j).self_of_nhds.symm



theorem fderiv (h : CompactSmoothConvergenceOn fseq f l U) :
    CompactSmoothConvergenceOn (fun i => _root_.fderiv ℝ (fseq i)) (_root_.fderiv ℝ f) l U where
  isOpen := h.isOpen
  smooth := h.smooth.fderiv_of_isOpen h.isOpen (by simp)
  eventually_smooth K hK hKU := (h.eventually_smooth K hK hKU).mono
    fun i hi x hx => (hi x hx).fderiv_right (m := ∞) (by simp)
  jets j K hK hKU := tendstoUniformlyOn_iteratedFDeriv_fderiv (h.jets (j + 1) K hK hKU)



theorem prodMk (hf : CompactSmoothConvergenceOn fseq f l U)
    {gseq : ι → E → G} {g : E → G} (hg : CompactSmoothConvergenceOn gseq g l U) :
    CompactSmoothConvergenceOn (fun i x => (fseq i x, gseq i x)) (fun x => (f x, g x)) l U where
  isOpen := hf.isOpen
  smooth := hf.smooth.prodMk hg.smooth
  eventually_smooth K hK hKU := by
    filter_upwards [hf.eventually_smooth K hK hKU, hg.eventually_smooth K hK hKU] with i hi hgi
    exact fun x hx => (hi x hx).prodMk (hgi x hx)
  jets j K hK hKU := tendstoUniformlyOn_iteratedFDeriv_prodMk j
    (fun x hx => hf.smooth.contDiffAt (hf.isOpen.mem_nhds (hKU hx)))
    (fun x hx => hg.smooth.contDiffAt (hg.isOpen.mem_nhds (hKU hx)))
    (hf.eventually_smooth K hK hKU) (hg.eventually_smooth K hK hKU)
    (hf.jets j K hK hKU) (hg.jets j K hK hKU)


theorem constant (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    CompactSmoothConvergenceOn (fun _ : ι => f) f l U where
  isOpen := hU
  smooth := hf
  eventually_smooth K _ hKU := Eventually.of_forall
    (fun _ x hx => hf.contDiffAt (hU.mem_nhds (hKU hx)))
  jets _ _ _ _ := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    exact Eventually.of_forall fun _ _ _ => by simpa only [dist_self] using hepsilon



theorem of_tendsto_const {a : ι → F} {b : F} (hab : Tendsto a l (𝓝 b)) (hU : IsOpen U) :
    CompactSmoothConvergenceOn (fun i => fun _ : E => a i) (fun _ => b) l U where
  isOpen := hU
  smooth := contDiffOn_const
  eventually_smooth _ _ _ := Eventually.of_forall fun _ _ _ => contDiffAt_const
  jets j K _ _ := by
    cases j with
    | zero =>
      have hc := (continuousMultilinearCurryFin0 ℝ E F).symm.isometry.uniformContinuous
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
        hc.comp_tendstoUniformlyOn (hab.tendstoUniformlyOn_const K)
    | succ j =>
      simp only [iteratedFDeriv_succ_const]
      exact tendsto_const_nhds.tendstoUniformlyOn_const K



theorem comp_continuousLinearMap (h : CompactSmoothConvergenceOn fseq f l U)
    (L : G →L[ℝ] E) :
    CompactSmoothConvergenceOn (fun i => fseq i ∘ L) (f ∘ L) l (L ⁻¹' U) where
  isOpen := h.isOpen.preimage L.continuous
  smooth := h.smooth.comp_continuousLinearMap L
  eventually_smooth K hK hKU := by
    filter_upwards [h.eventually_smooth (L '' K) (hK.image L.continuous)
      (image_subset_iff.mpr hKU)] with i hi
    exact fun x hx => (hi (L x) (mem_image_of_mem L hx)).comp x L.contDiff.contDiffAt
  jets j K hK hKU := by
    have hconv := ((h.jets j (L '' K) (hK.image L.continuous)
      (image_subset_iff.mpr hKU)).comp L).mono (subset_preimage_image L K)
    have hread := (ContinuousMultilinearMap.compContinuousLinearMapL
      (F := F) (fun _ : Fin j => L)).uniformContinuous.comp_tendstoUniformlyOn hconv
    apply (hread.congr ?_).congr_right ?_
    · filter_upwards [h.eventually_smooth (L '' K) (hK.image L.continuous)
        (image_subset_iff.mpr hKU)] with i hi
      intro x hx
      exact (Poincare.Analysis.Calculus.iteratedFDeriv_comp_continuousLinearMap_of_contDiffAt L
        (hi (L x) (mem_image_of_mem L hx)) j).symm
    · intro x hx
      exact (Poincare.Analysis.Calculus.iteratedFDeriv_comp_continuousLinearMap_of_contDiffAt L
        (h.smooth.contDiffAt (h.isOpen.mem_nhds (hKU hx))) j).symm

end CompactSmoothConvergenceOn



theorem CompactSmoothConvergenceOn.comp_smooth
    {E F G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {ι : Type*} {l : Filter ι} {U : Set E} {V : Set F}
    {fseq : ι → E → F} {f : E → F} {g : F → G}
    (h : CompactSmoothConvergenceOn fseq f l U)
    (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V) (hfV : MapsTo f U V) :
    CompactSmoothConvergenceOn (fun i => g ∘ fseq i) (g ∘ f) l U where
  isOpen := h.isOpen
  smooth := hg.comp h.smooth hfV
  eventually_smooth K hK hKU := by
    have hfit := (h.uniformlyOn hK hKU).eventually_mapsTo_of_compact_image
      (hK.image_of_continuousOn (h.smooth.continuousOn.mono hKU)) hV (fun x hx => hfV (hKU hx))
    filter_upwards [h.eventually_smooth K hK hKU, hfit] with i hi him
    exact fun x hx => (hg.contDiffAt (hV.mem_nhds (him hx))).comp x (hi x hx)
  jets j K hK hKU := tendstoUniformlyOn_iteratedFDeriv_comp_of_compact j hK hV
    (fun x hx => h.smooth.contDiffAt (h.isOpen.mem_nhds (hKU hx))) hg
    (fun x hx => hfV (hKU hx)) (h.eventually_smooth K hK hKU)
    (fun m _ => h.jets m K hK hKU)



theorem Filter.Tendsto.compactSmoothConvergenceOn_clm_apply
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {ι : Type*} {l : Filter ι} {Lseq : ι → E →L[ℝ] F} {L : E →L[ℝ] F}
    (h : Tendsto Lseq l (𝓝 L)) :
    CompactSmoothConvergenceOn (fun i x => Lseq i x) (fun x => L x) l univ := by
  have hc : CompactSmoothConvergenceOn (fun i => fun _ : E => Lseq i)
      (fun _ => L) l univ :=
    CompactSmoothConvergenceOn.of_tendsto_const h isOpen_univ
  have hi : CompactSmoothConvergenceOn (fun _ : ι => (id : E → E)) id l univ :=
    CompactSmoothConvergenceOn.constant isOpen_univ contDiff_id.contDiffOn
  have heval : ContDiff ℝ ∞ (fun z : (E →L[ℝ] F) × E => z.1 z.2) :=
    contDiff_fst.clm_apply contDiff_snd
  exact (hc.prodMk hi).comp_smooth isOpen_univ heval.contDiffOn (fun _ _ => mem_univ _)
