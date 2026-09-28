import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Tubes.Branches.EmbeddedNeighborhood











set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
local notation "V3" => (Fin 3 → ℝ)



theorem SourceDoubleComponents.exists_paired_source_neighborhoods
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {sourceSet rimSet : Set E} [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    (old : SourceDoubleComponents e f sourceSet rimSet R) (hf : PolyhedralPLInCharts e f sourceSet)
    {A B : Set E} {T : Set X} (hA : IsCompact A) (hB : IsCompact B)
    (hAG : A ⊆ doubleLocusOn f sourceSet) (hBG : B ⊆ doubleLocusOn f sourceSet)
    (hAB : Disjoint A B) (hiA : InjOn f A) (hiB : InjOn f B)
    (hfull : ∀ x ∈ sourceSet, f x ∈ T ↔ x ∈ A ∪ B) :
    ∃ (P Q : SimplicialComplex ℝ E) (U V : Set sourceSet) (O : Set X),
      P.faces.Finite ∧ Q.faces.Finite ∧ P.space ⊆ sourceSet ∧ Q.space ⊆ sourceSet ∧
      Disjoint P.space Q.space ∧ IsOpen U ∧ IsOpen V ∧
      (Subtype.val : sourceSet → E) ⁻¹' A ⊆ U ∧
      (Subtype.val : sourceSet → E) ⁻¹' B ⊆ V ∧
      Subtype.val '' U ⊆ P.space ∧ Subtype.val '' V ⊆ Q.space ∧
      IsEmbedding (fun x : P.space ↦ f x) ∧ IsEmbedding (fun x : Q.space ↦ f x) ∧
      PolyhedralPLInCharts e f P.space ∧ PolyhedralPLInCharts e f Q.space ∧
      IsOpen O ∧ T ⊆ O ∧ ∀ x ∈ sourceSet, f x ∈ O → x ∈ P.space ∪ Q.space := by
  let : CompactSpace sourceSet := isCompact_iff_compactSpace.mp
    (old.source_space ▸ old.source.isCompact_space_of_finite old.source_finite)
  obtain ⟨W, Z, hWo, hZo, hAW, hBZ, hWZ⟩ :=
    normal_separation hA.isClosed hB.isClosed hAB
  obtain ⟨P, U, hP, hPW, hUo, hAU, hUP, hPi, hPPL⟩ :=
    old.exists_finite_embedded_source_neighborhood hf hA hAG hiA
      (hWo.preimage continuous_subtype_val) hAW
  obtain ⟨Q, V, hQ, hQZ, hVo, hBV, hVQ, hQi, hQPL⟩ :=
    old.exists_finite_embedded_source_neighborhood hf hB hBG hiB
      (hZo.preimage continuous_subtype_val) hBZ
  have hfc : Continuous (fun x : sourceSet ↦ f x) :=
    hf.continuousOn.comp_continuous continuous_subtype_val (fun x ↦ x.property)
  let O : Set X := ((fun x : sourceSet ↦ f x) '' (U ∪ V)ᶜ)ᶜ
  have hOo : IsOpen O := (((hUo.union hVo).isClosed_compl.isCompact).image hfc).isClosed.isOpen_compl
  have hTO : T ⊆ O := by
    intro y hy
    rintro ⟨x, hx, hxy⟩
    have hxT : f x ∈ T := by
      rw [show f x = y from hxy]
      exact hy
    rcases (hfull x x.property).mp hxT with ha | hb
    · exact hx (Or.inl (hAU ha))
    · exact hx (Or.inr (hBV hb))
  refine ⟨P, Q, U, V, O, hP, hQ, fun _ hx ↦ (hPW hx).1,
    fun _ hx ↦ (hQZ hx).1, hWZ.mono (fun _ hx ↦ (hPW hx).2)
      (fun _ hx ↦ (hQZ hx).2), hUo, hVo, hAU, hBV, hUP, hVQ,
    hPi, hQi, hPPL, hQPL, hOo, hTO, ?_⟩
  intro x hx hfx
  have hUV : (⟨x, hx⟩ : sourceSet) ∈ U ∪ V := by
    by_contra hn
    exact hfx ⟨⟨x, hx⟩, hn, rfl⟩
  exact hUV.elim (fun h ↦ Or.inl (hUP ⟨⟨x, hx⟩, h, rfl⟩))
    (fun h ↦ Or.inr (hVQ ⟨⟨x, hx⟩, h, rfl⟩))
end PoincareConjecture.M76.Dehn.Annuli
