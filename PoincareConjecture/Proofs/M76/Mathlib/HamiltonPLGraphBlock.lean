import PoincareConjecture.Proofs.M76.Mathlib.CompactPLGraphCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineGroupoid

set_option autoImplicit false

open Set Geometry Filter
open scoped Topology

namespace OpenPartialHomeomorph

variable {M E : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_compactly_supported_PL_graph_block
    (e : OpenPartialHomeomorph M E) {A : Set M}
    (hA : IsCompact A) (hAe : A ⊆ e.source) :
    ∃ (f : M → ℝ × E) (C : Set M), IsCompact C ∧ C ⊆ e.source ∧
      Continuous f ∧ (∀ x, x ∉ C → f x = 0) ∧
      EqOn f (fun x => (1, e x)) A ∧
      (∀ x, 0 ≤ (f x).1 ∧ (f x).1 ≤ 1) ∧
      (∀ x, (f x).1 = 1 → x ∈ e.source ∧ (f x).2 = e x) ∧
      (∀ d : OpenPartialHomeomorph M E, d.symm.trans e ∈ piecewiseAffineGroupoid E →
        LocallyPiecewiseAffineOn (f ∘ d.symm) d.target) := by
  classical
  have hQ : IsCompact (e '' A) :=
    hA.image_of_continuousOn (e.continuousOn.mono hAe)
  have hQt : e '' A ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.mapsTo (hAe hx)
  obtain ⟨g, K, hK, hKt, _, hgeq, hgoff, hgcont, hgPL, hgbound, hgrecover⟩ :=
    SimplicialComplex.exists_locallyPL_supported_graph_extension hQ e.open_target hQt
  let C : Set M := e.symm '' K.space
  have hC : IsCompact C := (K.isCompact_space_of_finite hK).image_of_continuousOn
    (e.symm.continuousOn.mono hKt)
  have hCe : C ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.symm.mapsTo (hKt hy)
  let f : M → ℝ × E := e.source.indicator (fun x => g (e x))
  have hfon (x : M) (hx : x ∈ e.source) : f x = g (e x) := indicator_of_mem hx _
  have hfoff (x : M) (hx : x ∉ e.source) : f x = 0 := indicator_of_notMem hx _
  have hfzero (x : M) (hx : x ∉ C) : f x = 0 := by
    by_cases hxe : x ∈ e.source
    · rw [hfon x hxe]
      apply hgoff
      intro hxK
      exact hx ⟨e x, hxK, e.left_inv hxe⟩
    · exact hfoff x hxe
  have hfcont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hxe : x ∈ e.source
    · apply (hgcont.continuousAt.comp (e.continuousAt hxe)).congr
      filter_upwards [e.open_source.mem_nhds hxe] with y hye
      exact (hfon y hye).symm
    · have hxC : x ∉ C := fun hx => hxe (hCe hx)
      apply (continuousAt_const : ContinuousAt (fun _ : M => (0 : ℝ × E)) x).congr_of_eventuallyEq
      filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hxC] with y hyC
      exact hfzero y hyC
  refine ⟨f, C, hC, hCe, hfcont, hfzero, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hfon x (hAe hx)]
    exact hgeq ⟨x, hx, rfl⟩
  · intro x
    by_cases hx : x ∈ e.source
    · rw [hfon x hx]
      exact hgbound (e x)
    · simp [hfoff x hx]
  · intro x hxone
    by_cases hx : x ∈ e.source
    · refine ⟨hx, ?_⟩
      rw [hfon x hx] at hxone ⊢
      exact hgrecover (e x) hxone
    · simp [hfoff x hx] at hxone
  · intro d hde
    let t := d.symm.trans e
    have htPL : LocallyPiecewiseAffineOn (t : E → E) t.source :=
      ((mem_piecewiseAffineGroupoid_iff E t).mp hde).1
    have hcomp : LocallyPiecewiseAffineOn (g ∘ t) t.source := by
      simpa only [preimage_univ, inter_univ] using hgPL.comp htPL
    have hlocal : LocallyPiecewiseAffineOn (f ∘ d.symm) t.source := by
      apply hcomp.congr
      intro y hy
      exact (hfon (d.symm y) hy.2).symm
    let W : Set E := d.target ∩ d.symm ⁻¹' Cᶜ
    have hW : IsOpen W := d.symm.continuousOn.isOpen_inter_preimage
      d.open_target hC.isClosed.isOpen_compl
    have hWPL : LocallyPiecewiseAffineOn (f ∘ d.symm) W := by
      apply (locallyPiecewiseAffineOn_affine
        (ContinuousAffineMap.const ℝ E (0 : ℝ × E)) hW).congr
      intro y hy
      exact (hfzero (d.symm y) hy.2).symm
    apply LocallyPiecewiseAffineOn.locality
    intro y hy
    by_cases hye : d.symm y ∈ e.source
    · exact ⟨t.source, ⟨hy, hye⟩,
        hlocal.mono (d.open_target.inter t.open_source) inter_subset_right⟩
    · refine ⟨W, ⟨hy, ?_⟩,
        hWPL.mono (d.open_target.inter hW) inter_subset_right⟩
      exact fun hyC => hye (hCe hyC)

end OpenPartialHomeomorph
