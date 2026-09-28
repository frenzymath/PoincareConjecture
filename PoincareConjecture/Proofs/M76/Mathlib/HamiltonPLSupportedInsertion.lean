import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLAtlasCorrection
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLAtlasInsertion










set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {M E ι : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]






theorem exists_supported_compact_core_chart_insertion
    (c : ι → OpenPartialHomeomorph M E) (d : OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (c i).symm.trans (c j) ∈ piecewiseAffineGroupoid E)
    {A B N K : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hN : IsOpen N) (hK : IsClosed K)
    (hAU : A ⊆ ⋃ i, (c i).source) (hBV : B ⊆ d.source) (hAB : A ∩ B ⊆ N)
    (hKU : K ⊆ (⋃ i, (c i).source) ∩ d.source)
    (h : ((⋃ i, (c i).source) ∩ d.source : Set M) ≃ₜ
      ((⋃ i, (c i).source) ∩ d.source : Set M))
    (hfix : ∀ x : ((⋃ i, (c i).source) ∩ d.source : Set M),
      (x : M) ∉ K → h x = x)
    (F : M → E)
    (hF : ∀ x : ((⋃ i, (c i).source) ∩ d.source : Set M), F x = d (h x))
    (hstraight : ∀ i, LocallyPiecewiseAffineOn (F ∘ (c i).symm)
      ((c i).target ∩ (c i).symm ⁻¹' N)) :
    ∃ (H : M ≃ₜ M) (U V : Set M) (C : Option ι → OpenPartialHomeomorph M E),
      (∀ x : ((⋃ i, (c i).source) ∩ d.source : Set M), H x = (h x : M)) ∧
      EqOn (H : M → M) id Kᶜ ∧
      H ⁻¹' (⋃ i, (c i).source) = ⋃ i, (c i).source ∧
      (H.transOpenPartialHomeomorph d).source = d.source ∧
      (H.transOpenPartialHomeomorph d).target = d.target ∧
      EqOn (H.transOpenPartialHomeomorph d : M → E) d Kᶜ ∧
      IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧
      U ⊆ ⋃ i, (c i).source ∧ V ⊆ d.source ∧ U ∩ V ⊆ N ∧
      C none = (H.transOpenPartialHomeomorph d).restr V ∧
      (∀ i, C (some i) = (c i).restr U) ∧
      (∀ i j, (C i).symm.trans (C j) ∈ piecewiseAffineGroupoid E) ∧
      (⋃ i, (C i).source) = U ∪ V := by
  obtain ⟨H, hlocal, hfixed, hpres, hsource, htarget, hcorrect, hoff⟩ :=
    d.exists_supported_overlap_chart_correction
      (isOpen_iUnion fun i => (c i).open_source) hK hKU h hfix
  let e := H.transOpenPartialHomeomorph d
  have hPL (i : ι) : (c i).symm.trans (e.restr N) ∈ piecewiseAffineGroupoid E := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    have hmono : LocallyPiecewiseAffineOn (F ∘ (c i).symm)
        ((c i).symm.trans (e.restr N)).source :=
      (hstraight i).mono ((c i).symm.trans (e.restr N)).open_source
        (fun x hx => by
          refine ⟨hx.1, ?_⟩
          change (c i).symm x ∈ N
          exact interior_subset hx.2.2)
    apply hmono.congr
    intro x hx
    have hxU : (c i).symm x ∈ ⋃ j, (c j).source :=
      mem_iUnion.mpr ⟨i, (c i).map_target hx.1⟩
    have hxV : (c i).symm x ∈ d.source := hsource.subset hx.2.1
    let y : ((⋃ j, (c j).source) ∩ d.source : Set M) :=
      ⟨(c i).symm x, hxU, hxV⟩
    change F ((c i).symm x) = e ((c i).symm x)
    exact (hF y).trans (hcorrect y).symm
  have hBe : B ⊆ e.source := hBV.trans hsource.symm.subset
  obtain ⟨U, V, C, hU, hV, hAC, hBC, hUc, hVe, hUV, hCn, hCs, hCC, hcover⟩ :=
    exists_compact_core_chart_insertion c e hcompat hA hB hN hAU hBe hAB hPL
  exact ⟨H, U, V, C, hlocal, hfixed, hpres, hsource, htarget, hoff,
    hU, hV, hAC, hBC, hUc, hVe.trans hsource.subset, hUV, hCn, hCs, hCC, hcover⟩

end OpenPartialHomeomorph
