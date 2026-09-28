import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.EndpointOrder
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Tubes.Strips.RimEnds
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Components.LiteralPartner



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "source" => PolygonalCrossingResolution.source

theorem SourceDoubleComponents.exists_oriented_spanning_tube
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {S : Set E} {R W : Set X}
    (Q : Bool → Set E) (mark : Bool → Set X)
    (M : SourceDoubleComponents e f S (Q false ∪ Q true) R)
    (hf : PolyhedralPLInCharts e f S) (he : PLDomain e R) (i : M.Index)
    (hQ : ∀ b, IsClosed (Q b)) (hQdis : Disjoint (Q false) (Q true))
    (hmarkdis : Disjoint (mark false) (mark true))
    (hmark : ∀ b, MapsTo f (S ∩ Q b) (mark b))
    (hin : MapsTo f S R) (hfront : ∀ x ∈ S, f x ∈ frontier R ↔ x ∈ Q false ∪ Q true)
    (hmeet0 : (M.pieces i ∩ Q false).Nonempty) (hmeet1 : (M.pieces i ∩ Q true).Nonempty)
    (hW : IsOpen W) (hAW : f '' M.pieces i ⊆ W) :
    ∃ (c : Bool → P2 → E) (τ : C3 → X),
      (∀ j, FinitePiecewiseAffineOn (c j) source ∧ InjOn (c j) source ∧ MapsTo (c j) source S) ∧
      Disjoint (c false '' source) (c true '' source) ∧
      PolyhedralPLInCharts e τ tube ∧ InjOn τ tube ∧ MapsTo τ tube R ∧ MapsTo τ tube W ∧
      (∀ j p, p ∈ source → f (c j p) = τ (originalStripSheet j p)) ∧
      S ∩ f ⁻¹' (τ '' tube) = c false '' source ∪ c true '' source ∧
      (∀ j, c j '' arm 0 = M.pieces (if j then M.mate i else i)) ∧
      (∀ z ∈ tube, τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1) ∧
      (∀ j p, p ∈ source → (c j p ∈ Q false ↔ p.1 = 0)) ∧
      (∀ j p, p ∈ source → (c j p ∈ Q true ↔ p.1 = 1)) := by
  have hball := (M.interval_iff_meets_rim i).mpr
    (hmeet0.mono (inter_subset_inter_right _ subset_union_left))
  obtain ⟨c, τ, hcs, hdis, hτ, hτemb, hτR, hτW, hval, hfull, hcenter, hτfront, hrim⟩ :=
    M.exists_interval_tube_source_strips hf he i hball hin hfront hW hAW
  have hci (j : Bool) : InjOn (c j) source := by
    intro x hx y hy h
    exact congrArg Subtype.val ((hcs j).2.1.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)
  have hτi : InjOn τ tube := by
    intro x hx y hy h
    exact congrArg Subtype.val (hτemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)
  have hpair (t : I) : f (c false (t, 0)) = f (c true (t, 0)) := by
    rw [hval false _ ⟨t.property, by norm_num⟩, hval true _ ⟨t.property, by norm_num⟩]
    simp [originalStripSheet]
  have hm0 : (c false '' arm 0 ∩ Q false).Nonempty := by simpa [hcenter] using hmeet0
  have hm1 : (c false '' arm 0 ∩ Q true).Nonempty := by simpa [hcenter] using hmeet1
  rcases paired_spanning_center_endpoint_order Q mark f c (fun j ↦ (hcs j).2.2)
    hQdis hmarkdis hmark hrim hpair hm0 hm1 with horder | horder
  · have hs (j : Bool) := proper_strip_separate_rims (hcs j).1.continuousOn
      (hQ false) (hQ true) hQdis (hrim j) (horder j).1 (horder j).2
    exact ⟨c, τ, fun j ↦ ⟨(hcs j).1, hci j, (hcs j).2.2⟩, hdis, hτ, hτi,
      hτR, hτW, hval, hfull, hcenter, hτfront, fun j ↦ (hs j).1, fun j ↦ (hs j).2⟩
  · let c' (j : Bool) := c j ∘ spanningSourceReverse
    let τ' := τ ∘ spanningTubeReverse
    have hc' (j : Bool) : FinitePiecewiseAffineOn (c' j) source :=
      (hcs j).1.comp spanningSourceReverse_finitePL spanningSourceReverse_mapsTo
    have hci' (j : Bool) : InjOn (c' j) source := by
      intro x hx y hy hxy
      exact spanningSourceReverse_involutive.injective
        (hci j (spanningSourceReverse_mapsTo hx) (spanningSourceReverse_mapsTo hy) hxy)
    have hcS' (j : Bool) : MapsTo (c' j) source S :=
      (hcs j).2.2.comp spanningSourceReverse_mapsTo
    have him (j : Bool) : c' j '' source = c j '' source := by
      rw [show c' j = c j ∘ spanningSourceReverse from rfl, image_comp, spanningSourceReverse_image]
    have htimage : τ' '' tube = τ '' tube := by
      rw [show τ' = τ ∘ spanningTubeReverse from rfl, image_comp, spanningTubeReverse_image]
    have ht' : InjOn τ' tube := by
      intro x hx y hy hxy
      exact spanningTubeReverse_involutive.injective
        (hτi (spanningTubeReverse_mapsTo hx) (spanningTubeReverse_mapsTo hy) hxy)
    have hrim' (j : Bool) (p : P2) (hp : p ∈ source) :
        c' j p ∈ Q false ∪ Q true ↔ p.1 = 0 ∨ p.1 = 1 := by
      change c j (spanningSourceReverse p) ∈ Q false ∪ Q true ↔ _
      rw [hrim j _ (spanningSourceReverse_mapsTo hp), spanningSourceReverse_apply]
      dsimp only
      constructor <;> rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    have hs (j : Bool) := proper_strip_separate_rims (hc' j).continuousOn
      (hQ false) (hQ true) hQdis (hrim' j)
      (show c' j (0, 0) ∈ Q false by simpa [c', spanningSourceReverse_apply] using (horder j).2)
      (show c' j (1, 0) ∈ Q true by simpa [c', spanningSourceReverse_apply] using (horder j).1)
    refine ⟨c', τ', fun j ↦ ⟨hc' j, hci' j, hcS' j⟩, ?_, spanningTubeReverse_polyhedralPL hτ,
      ht', hτR.comp spanningTubeReverse_mapsTo, hτW.comp spanningTubeReverse_mapsTo,
      ?_, ?_, ?_, ?_, fun j ↦ (hs j).1, fun j ↦ (hs j).2⟩
    · simpa only [him] using hdis
    · intro j p hp
      exact hval j _ (spanningSourceReverse_mapsTo hp)
    · simpa only [htimage, him] using hfull
    · intro j
      rw [show c' j = c j ∘ spanningSourceReverse from rfl, image_comp, spanningSourceReverse_arm_image]
      exact hcenter j
    · intro z hz
      change τ (spanningTubeReverse z) ∈ frontier R ↔ _
      rw [hτfront _ (spanningTubeReverse_mapsTo hz), spanningTubeReverse_apply]
      dsimp only
      constructor <;> rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)

end PoincareConjecture.M76.Dehn.Annuli
