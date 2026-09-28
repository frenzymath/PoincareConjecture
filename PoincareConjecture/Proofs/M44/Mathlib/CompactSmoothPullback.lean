import PoincareConjecture.Proofs.M44.Mathlib.CompactSmoothConvergence
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.DomainChange

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace CompactSmoothConvergenceOn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem locally_eventually_smooth
    {ι : Type*} {l : Filter ι} {fseq : ι → E → F} {f : E → F} {U : Set E}
    (h : CompactSmoothConvergenceOn fseq f l U) {x : E} (hx : x ∈ U) :
    ∃ W, IsOpen W ∧ x ∈ W ∧ ∀ᶠ i in l, ContDiffOn ℝ ∞ (fseq i) W := by
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_between isCompact_singleton h.isOpen
    (singleton_subset_iff.mpr hx)
  refine ⟨interior K, isOpen_interior, hxK (mem_singleton x), ?_⟩
  filter_upwards [h.eventually_smooth K hK hKU] with i hi
  exact fun y hy => (hi y (interior_subset hy)).contDiffWithinAt

theorem comp [FiniteDimensional ℝ F]
    {fseq : ℕ → E → F} {f : E → F} {gseq : ℕ → E → E} {g : E → E} {U V : Set E}
    (hf : CompactSmoothConvergenceOn fseq f atTop U)
    (hg : CompactSmoothConvergenceOn gseq g atTop V) (hgU : MapsTo g V U) :
    CompactSmoothConvergenceOn (fun n => fseq n ∘ gseq n) (f ∘ g) atTop V := by
  obtain ⟨hlocal, hjet⟩ :=
    Poincare.Analysis.Calculus.smooth_convergence_comp_on_finiteDimensional
      hf.isOpen hg.isOpen hf.smooth hg.smooth hgU
      (fun _ hx => hf.locally_eventually_smooth hx)
      (fun _ hx => hg.locally_eventually_smooth hx) hf.jets hg.jets
  refine ⟨hg.isOpen, hf.smooth.comp hg.smooth hgU, ?_, hjet⟩
  intro K hK hKV
  exact Poincare.Analysis.Calculus.eventually_contDiffAt_on_compact hK hKV
    (fun x hx => let ⟨W, hW, hxW, _, hs⟩ := hlocal x hx; ⟨W, hW, hxW, hs⟩)

theorem pullback_bilinear
    {Bseq : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ} {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    {aseq : ℕ → E → E} {a : E → E} {U V : Set E}
    (hB : CompactSmoothConvergenceOn Bseq B atTop U)
    (ha : CompactSmoothConvergenceOn aseq a atTop V) (haU : MapsTo a V U) :
    CompactSmoothConvergenceOn
      (fun n x => (Bseq n (aseq n x)).bilinearComp
        (_root_.fderiv ℝ (aseq n) x) (_root_.fderiv ℝ (aseq n) x))
      (fun x => (B (a x)).bilinearComp (_root_.fderiv ℝ a x) (_root_.fderiv ℝ a x)) atTop V := by
  obtain ⟨hlocal, hjet⟩ :=
    Poincare.Analysis.Calculus.smooth_convergence_pullback_bilinear_on_finiteDimensional
      hB.isOpen ha.isOpen hB.smooth ha.smooth haU
      (fun _ hx => hB.locally_eventually_smooth hx)
      (fun _ hx => ha.locally_eventually_smooth hx) hB.jets ha.jets
  have hbase : ContDiffOn ℝ ∞ (fun x => B (a x)) V := hB.smooth.comp ha.smooth haU
  have hd : ContDiffOn ℝ ∞ (_root_.fderiv ℝ a) V :=
    ha.smooth.fderiv_of_isOpen ha.isOpen (by simp)
  have hsmooth : ContDiffOn ℝ ∞
      (fun x => (B (a x)).bilinearComp (_root_.fderiv ℝ a x) (_root_.fderiv ℝ a x)) V := by
    have hf : ContDiff ℝ ∞ (fun L : E →L[ℝ] E →L[ℝ] ℝ => L.flip) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).contDiff
    simpa only [ContinuousLinearMap.bilinearComp, Function.comp_def] using
      hf.comp_contDiffOn ((hf.comp_contDiffOn (hbase.clm_comp hd)).clm_comp hd)
  refine ⟨ha.isOpen, hsmooth, ?_, hjet⟩
  intro K hK hKV
  exact Poincare.Analysis.Calculus.eventually_contDiffAt_on_compact hK hKV
    (fun x hx => let ⟨W, hW, hxW, _, hs⟩ := hlocal x hx; ⟨W, hW, hxW, hs⟩)

end CompactSmoothConvergenceOn
