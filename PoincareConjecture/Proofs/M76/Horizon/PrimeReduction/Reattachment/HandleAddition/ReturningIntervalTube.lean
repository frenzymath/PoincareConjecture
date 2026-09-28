import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Source.OrientedTube
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.ReturningDiskSideOrientation



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_returning_disk_region_strip_orientation
    {A B Q : Set P2} {c : P2 → P2}
    (hA : IsFinitePLBallPair P2 A Q) (hB : IsClosed B)
    (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hcAB : c '' source ⊆ A ∪ B) (hinter : A ∩ B = c '' arm 0)
    (hcenter : c '' arm 0 ⊆ Q) :
    ∃ s : Bool,
      (c ∘ returningStripOrientation s) '' halfSource true ⊆ A ∧
      (c ∘ returningStripOrientation s) '' halfSource false ⊆ B := by
  rcases strip_halves_on_opposite_disk_region_sides hA hB c hc hci hcAB hinter hcenter with h | h
  · refine ⟨false,?_,?_⟩
    · rw [image_comp,returningStripOrientation_image_half]
      exact h.1
    · rw [image_comp,returningStripOrientation_image_half]
      exact h.2
  · refine ⟨true,?_,?_⟩
    · rw [image_comp,returningStripOrientation_image_half]
      exact h.2
    · rw [image_comp,returningStripOrientation_image_half]
      exact h.1

theorem exists_disk_region_oriented_original_interval_tube
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R O : Set X}
    {S T C D D₀ B₀ D₁ B₁ U₀ V₀ U₁ : Set P2} {f₀ f₁ : P2 → X}
    (I : OriginalIntervalTube e R O S T C D f₀ f₁)
    (hD₀ : IsFinitePLBallPair P2 D₀ (U₀ ∪ C))
    (hB₀ : IsFinitePLBallPair P2 B₀ (C ∪ V₀))
    (hD₁ : IsFinitePLBallPair P2 D₁ (U₁ ∪ D))
    (hB₁ : IsClosed B₁)
    (hcover₀ : S ⊆ D₀ ∪ B₀) (hcover₁ : T ⊆ D₁ ∪ B₁)
    (hcommon₀ : D₀ ∩ B₀ = C) (hcommon₁ : D₁ ∩ B₁ = D) :
    ∃ (c₀ c₁ : P2 → P2) (τ : C3 → X),
      FinitePiecewiseAffineOn c₀ source ∧ FinitePiecewiseAffineOn c₁ source ∧
      IsEmbedding (fun p : source ↦ c₀ p) ∧ IsEmbedding (fun p : source ↦ c₁ p) ∧
      MapsTo c₀ source S ∧ MapsTo c₁ source T ∧
      c₀ '' source = I.first '' source ∧ c₁ '' source = I.second '' source ∧
      c₀ '' arm 0 = C ∧ c₁ '' arm 0 = D ∧
      c₀ '' halfSource true ⊆ D₀ ∧ c₀ '' halfSource false ⊆ B₀ ∧
      c₁ '' halfSource true ⊆ D₁ ∧ c₁ '' halfSource false ⊆ B₁ ∧
      PolyhedralPLInCharts e τ tube ∧ IsEmbedding (fun z : tube ↦ τ z) ∧
      MapsTo τ tube R ∧ MapsTo τ tube O ∧ τ '' tube = I.map '' tube ∧
      (∀ p ∈ source, f₀ (c₀ p) = τ ((p.2, -p.2), p.1)) ∧
      (∀ p ∈ source, f₁ (c₁ p) = τ ((p.2, p.2), p.1)) ∧
      (∀ z ∈ tube, τ z ∈ f₀ '' S ↔ z.1.2 = -z.1.1) ∧
      (∀ z ∈ tube, τ z ∈ f₁ '' T ↔ z.1.2 = z.1.1) ∧
      (∀ z ∈ tube, τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1) := by
  have hfi : InjOn I.first source := fun x hx y hy h ↦
    congrArg Subtype.val (I.first_embedding.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)
  have hsi : InjOn I.second source := fun x hx y hy h ↦
    congrArg Subtype.val (I.second_embedding.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)
  obtain ⟨s₀, hs₀D, hs₀B⟩ := exists_returning_strip_cut_orientation hD₀ hB₀ I.first_pl hfi
    (I.first_mapsTo.image_subset.trans hcover₀) (hcommon₀.trans I.first_center.symm)
    (I.first_center.subset.trans subset_union_right) (I.first_center.subset.trans subset_union_left)
  obtain ⟨s₁, hs₁D, hs₁B⟩ := exists_returning_disk_region_strip_orientation hD₁ hB₁ I.second_pl hsi
    (I.second_mapsTo.image_subset.trans hcover₁) (hcommon₁.trans I.second_center.symm)
    (I.second_center.subset.trans subset_union_right)
  let c₀ := I.first ∘ returningStripOrientation s₀
  let c₁ := I.second ∘ returningStripOrientation s₁
  let τ := I.map ∘ tubeArmOrientation s₀ (!s₁)
  have hc₀ : c₀ '' source = I.first '' source := by
    rw [image_comp, returningStripOrientation_image_source]
  have hc₁ : c₁ '' source = I.second '' source := by
    rw [image_comp, returningStripOrientation_image_source]
  refine ⟨c₀, c₁, τ, returningStripOrientation_finitePL I.first_pl s₀,
    returningStripOrientation_finitePL I.second_pl s₁,
    returningStripOrientation_embedding I.first_embedding s₀,
    returningStripOrientation_embedding I.second_embedding s₁,
    (fun p hp ↦ I.first_mapsTo ((returningStripOrientation_mem_source s₀ p).mpr hp)),
    (fun p hp ↦ I.second_mapsTo ((returningStripOrientation_mem_source s₁ p).mpr hp)),
    hc₀, hc₁, ?_, ?_, hs₀D, hs₀B, hs₁D, hs₁B,
    reoriented_tube_polyhedralPL e I.pl s₀ (!s₁),
    reoriented_tube_embedding I.map I.embedding s₀ (!s₁),
    (fun z hz ↦ I.mapsTo_region ((tubeArmOrientation_mem_tube s₀ (!s₁) z).mpr hz)),
    (fun z hz ↦ I.mapsTo_neighborhood ((tubeArmOrientation_mem_tube s₀ (!s₁) z).mpr hz)),
    reoriented_tube_image I.map s₀ (!s₁), ?_, ?_, ?_, ?_, ?_⟩
  · rw [image_comp, returningStripOrientation_image_center, I.first_center]
  · rw [image_comp, returningStripOrientation_image_center, I.second_center]
  · intro p hp
    dsimp only [c₀, τ, Function.comp_apply]
    rw [(returning_tube_orientation_sheets s₀ s₁ p).1]
    exact I.first_sheet _ ((returningStripOrientation_mem_source s₀ p).mpr hp)
  · intro p hp
    dsimp only [c₁, τ, Function.comp_apply]
    rw [(returning_tube_orientation_sheets s₀ s₁ p).2]
    exact I.second_sheet _ ((returningStripOrientation_mem_source s₁ p).mpr hp)
  · intro z hz
    exact (I.first_trace _ ((tubeArmOrientation_mem_tube s₀ (!s₁) z).mpr hz)).trans
      (returning_tube_orientation_traces s₀ s₁ z).1
  · intro z hz
    exact (I.second_trace _ ((tubeArmOrientation_mem_tube s₀ (!s₁) z).mpr hz)).trans
      (returning_tube_orientation_traces s₀ s₁ z).2
  · intro z hz
    change I.map (tubeArmOrientation s₀ (!s₁) z) ∈ frontier R ↔ _
    simpa only [tubeArmOrientation_longitudinal] using
      I.frontier_iff _ ((tubeArmOrientation_mem_tube s₀ (!s₁) z).mpr hz)

end PoincareConjecture.M76.Dehn.Annuli
