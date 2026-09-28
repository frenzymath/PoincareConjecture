import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.SelectedComponents

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem SeparatedCircleSource.exists_whole_surface_neighborhood
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f₀ f₁ : P2 → X}
    {S₀ S₁ C₀ C₁ : Set P2} {R : Set X}
    (D : SeparatedCircleSource e f₀ f₁ S₀ S₁ C₀ C₁ R)
    (hS₀ : IsCompact S₀) (hS₁ : IsCompact S₁)
    (hf₀ : ContinuousOn f₀ S₀) (hf₁ : ContinuousOn f₁ S₁)
    (hf₀i : InjOn f₀ S₀) (hf₁i : InjOn f₁ S₁)
    (himage : f₀ '' C₀ = f₁ '' C₁) :
    ∃ O : Set X, IsOpen O ∧ f₀ '' C₀ ⊆ O ∧
      (∀ z ∈ O, z ∈ f₀ '' S₀ ↔ z ∈ f₀ '' D.first.space) ∧
      (∀ z ∈ O, z ∈ f₁ '' S₁ ↔ z ∈ f₁ '' D.second.space) := by
  let A := f₀ '' (S₀ \ interior D.first.space)
  let B := f₁ '' (S₁ \ interior D.second.space)
  have hA : IsClosed A :=
    ((hS₀.diff isOpen_interior).image_of_continuousOn (hf₀.mono sdiff_subset)).isClosed
  have hB : IsClosed B :=
    ((hS₁.diff isOpen_interior).image_of_continuousOn (hf₁.mono sdiff_subset)).isClosed
  have hsub₀ := D.first_subset.trans interior_subset
  have hsub₁ := D.second_subset.trans interior_subset
  refine ⟨(A ∪ B)ᶜ,(hA.union hB).isOpen_compl,?_,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩ (h | h)
    · obtain ⟨y,hy,hyx⟩ := h
      have hxy := hf₀i (hsub₀ (interior_subset (D.first_selected hx))) hy.1 hyx.symm
      exact hy.2 (hxy ▸ D.first_selected hx)
    · obtain ⟨z,hz,hzx⟩ := himage.subset ⟨x,hx,rfl⟩
      obtain ⟨y,hy,hyx⟩ := h
      have hzy := hf₁i (hsub₁ (interior_subset (D.second_selected hz))) hy.1 (hzx.trans hyx.symm)
      exact hy.2 (hzy ▸ D.second_selected hz)
  · intro z hz
    constructor
    · rintro ⟨x,hx,rfl⟩
      have hxi : x ∈ interior D.first.space := by
        by_contra hh
        exact hz (Or.inl ⟨x,⟨hx,hh⟩,rfl⟩)
      exact ⟨x,interior_subset hxi,rfl⟩
    · exact fun h => image_mono hsub₀ h
  · intro z hz
    constructor
    · rintro ⟨x,hx,rfl⟩
      have hxi : x ∈ interior D.second.space := by
        by_contra hh
        exact hz (Or.inr ⟨x,⟨hx,hh⟩,rfl⟩)
      exact ⟨x,interior_subset hxi,rfl⟩
    · exact fun h => image_mono hsub₁ h

theorem SeparatedCircleSource.exists_selected_identity_tube
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f₀ f₁ : P2 → X}
    {S₀ S₁ C₀ C₁ : Set P2} {R : Set X}
    (D : SeparatedCircleSource e f₀ f₁ S₀ S₁ C₀ C₁ R) (he : PLDomain e R)
    (hS₀ : IsCompact S₀) (hS₁ : IsCompact S₁)
    (hf₀ : ContinuousOn f₀ S₀) (hf₁ : ContinuousOn f₁ S₁)
    (hf₀i : InjOn f₀ S₀) (hf₁i : InjOn f₁ S₁)
    (hC₀ : IsCompact C₀) (hC₁ : IsCompact C₁) (hc₀ : IsConnected C₀)
    (himage : f₀ '' C₀ = f₁ '' C₁)
    {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) :
    ∃ (i : D.decomposition.Index)
      (T : ComponentIdentityAnnuliData (e := e) (R := R) D.decomposition i L d),
      D.decomposition.pieces i = C₀ ∧
      D.decomposition.pieces (D.decomposition.mate i) = D.shift '' C₁ ∧
      (∀ z ∈ T.tube '' _root_.Dehn.identityTube L d,
        z ∈ f₀ '' S₀ ↔ z ∈ f₀ '' D.first.space) ∧
      (∀ z ∈ T.tube '' _root_.Dehn.identityTube L d,
        z ∈ f₁ '' S₁ ↔ z ∈ f₁ '' D.second.space) := by
  obtain ⟨i,hi,hmi,hm⟩ := D.exists_selected_components hC₀ hC₁ hc₀ himage
  obtain ⟨O,hO,hCO,hfirst,hsecond⟩ :=
    D.exists_whole_surface_neighborhood hS₀ hS₁ hf₀ hf₁ hf₀i hf₁i himage
  have hselectedR : D.map '' D.decomposition.pieces i ⊆ interior R := by
    rintro _ ⟨x,hx,rfl⟩
    exact D.double_region (D.decomposition.piece_subset_double i hx)
  have hselectedO : D.map '' D.decomposition.pieces i ⊆ O := by
    rw [hi]
    rintro _ ⟨x,hx,rfl⟩
    rw [D.first_value (interior_subset (D.first_selected hx))]
    exact hCO ⟨x,hx,rfl⟩
  have hfront : Disjoint (D.map '' D.decomposition.pieces i)
      (D.map '' frontier D.source.space) := by
    apply disjoint_left.mpr
    rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
    have hyS : y ∈ D.source.space :=
      (D.source.isCompact_space_of_finite D.source_finite).isClosed.frontier_subset hy
    have hyD : y ∈ doubleLocusOn D.map D.source.space := by
      by_cases hxy : x = y
      · exact hxy ▸ D.decomposition.piece_subset_double i hx
      · exact ⟨hyS,x,D.decomposition.piece_subset_source i hx,hyz.trans hxz.symm,Ne.symm hxy⟩
    exact disjoint_interior_frontier.notMem_of_mem_left (D.double_interior hyD) hy
  obtain ⟨T,hTO⟩ := exists_identity_annuli_away_source_frontier
    D.source D.source_finite rfl D.decomposition D.map_PL he D.crossings i hm
    hselectedR hfront O hO hselectedO hd hwidth
  exact ⟨i,T,hi,hmi,fun z hz => hfirst z (hTO hz),fun z hz => hsecond z (hTO hz)⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
