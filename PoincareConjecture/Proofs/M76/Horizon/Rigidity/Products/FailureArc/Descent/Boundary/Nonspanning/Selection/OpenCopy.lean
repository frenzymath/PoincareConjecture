import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Selection.Retention
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Retention.Relation
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.OpenSourceCopy



set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.NonspanningStripExteriors

open PolygonalCrossingResolution NonspanningChainHole Annuli

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_retained_open_copy
    {c : Bool → P2 → P2} {D T : Set P2} (E : NonspanningStripExteriors c D T)
    (N : NonspanningChainAnnulus E.hole)
    (hD : IsFinitePLBallPair P2 D (frontier D))
    {X : Type*} {f g : P2 → X} {τ : C3 → X}
    (hc : ∀ j, ContinuousOn (c j) source) (hci : ∀ j, InjOn (c j) source)
    (hcS : ∀ j, MapsTo (c j) source (T \ interior D))
    (hdis : Disjoint (c false '' source) (c true '' source)) (hτ : InjOn τ tube)
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfull : (T \ interior D) ∩ f ⁻¹' (τ '' tube) = c false '' source ∪ c true '' source)
    (hkeep : ∀ i (x : E.hole.sourceSet i), g (N.copy i x) =
      pieceMap f (τ ∘ tubeArmOrientation E.s0 E.s1) i x) :
    ∃ (U V : Set P2) (H : U ≃ₜ V),
      U ⊆ N.retainedSet ∧ V ⊆ Ann ∧
      IsOpen ((Subtype.val : (T \ interior D : Set P2) → P2) ⁻¹' U) ∧
      IsOpen ((Subtype.val : Ann → P2) ⁻¹' V) ∧
      (∀ x : U, ∃ hx : (x : P2) ∈ N.retainedSet,
        (H x : P2) = N.retainedCopy E.disjoint_first_middle E.disjoint_first_last
          E.disjoint_middle_last ⟨x, hx⟩) ∧
      (∀ x : U, g (H x) = f x) ∧
      (∀ x : N.retainedSet, (x : P2) ∈ doubleLocusOn f (T \ interior D) → (x : P2) ∈ U) ∧
      doubleLocusOn g Ann ⊆ V := by
  let j := N.retainedCopy E.disjoint_first_middle E.disjoint_first_last E.disjoint_middle_last
  let oldStrips := c false '' source ∪ c true '' source
  let newStrips := range (N.sourceCopy (.inr false)) ∪ range (N.sourceCopy (.inr true))
  have hs : IsCompact source := isCompact_Icc.prod isCompact_Icc
  have hOld : IsClosed oldStrips :=
    (hs.image_of_continuousOn (hc false)).isClosed.union
      (hs.image_of_continuousOn (hc true)).isClosed
  have hNew : IsClosed newStrips := by
    let : ∀ b : Bool, CompactSpace (E.hole.sourceSet (.inr b)) :=
      fun _ ↦ isCompact_iff_compactSpace.mp hs
    exact (isCompact_range (N.sourceCopy_embedding (.inr false)).continuous).isClosed.union
      (isCompact_range (N.sourceCopy_embedding (.inr true)).continuous).isClosed
  have hK : IsCompact N.retainedSet :=
    ((E.first_ball.isCompact.diff isOpen_interior).union
      (E.middle_ball.isCompact.diff isOpen_interior)).union
        (E.last_ball.isCompact.diff isOpen_interior)
  obtain ⟨j', hj', hj'val⟩ := N.retainedCopy_PL E.disjoint_first_middle E.disjoint_first_last
    E.disjoint_middle_last E.retained_ball hD
  have hj : Continuous j := hj'.continuousOn.domRestrict.congr hj'val
  have hvalues : ∀ x, g (j x) = f x :=
    N.retainedCopy_values E.disjoint_first_middle E.disjoint_first_last E.disjoint_middle_last hkeep
  have hcover := N.retainedCopy_cover E.disjoint_first_middle E.disjoint_first_last E.disjoint_middle_last
  have hτ' : InjOn (τ ∘ tubeArmOrientation E.s0 E.s1) tube := by
    intro x hx y hy heq
    exact tubeArmOrientation_injective E.s0 E.s1
      (hτ ((tubeArmOrientation_mem_tube E.s0 E.s1 x).mpr hx)
        ((tubeArmOrientation_mem_tube E.s0 E.s1 y).mpr hy) heq)
  obtain ⟨hAtube, hMtube, hCtube⟩ := E.oriented_tube_preimages hfull
  have hcorners := E.oriented_corner_equations h0 h1
  have hnew := (N.retained_double_relation E.disjoint_first_middle E.disjoint_first_last
    E.disjoint_middle_last hkeep hτ' hAtube hMtube hCtube (fun t ↦ (hcorners t).1)
      (fun t ↦ (hcorners t).2.1) (fun t ↦ (hcorners t).2.2.1)
      (fun t ↦ (hcorners t).2.2.2)).2
  apply Annuli.exists_retained_open_source_copy E.retainedSource_subset hK hOld hNew j
    (N.retainedCopy_injective E.disjoint_first_middle E.disjoint_first_last E.disjoint_middle_last) hj
      (fun x ↦ hcover.subset (Or.inl ⟨x, rfl⟩)) hvalues
  · intro x hx
    rcases E.cover.symm.subset hx.1 with (hh | hh) | hh
    · rcases hh with hh | hh
      · exact Or.inl (Or.inl (Or.inl ⟨hh, hx.2⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨hh, hx.2⟩))
    · exact Or.inl (Or.inr ⟨hh, hx.2⟩)
    · exact Or.inr hh
  · exact hcover.symm.subset
  · intro x hx
    have hex : ∃ (b : Bool) (y : source), N.sourceCopy (.inr b) y = j x := by
      rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨false, y, hy⟩
      · exact ⟨true, y, hy⟩
    obtain ⟨b, y, hy⟩ := hex
    have hv : f x = (τ ∘ tubeArmOrientation E.s0 E.s1) (alternate (1 / 4) b y) := by
      rw [← hvalues x, ← hy]
      exact hkeep (.inr b) y
    apply hfull.subset
    refine ⟨E.retainedSource_subset x.property, ?_⟩
    refine ⟨tubeArmOrientation E.s0 E.s1 (alternate (1 / 4) b y), ?_, hv.symm⟩
    exact (tubeArmOrientation_mem_tube E.s0 E.s1 _).mpr
      ((mapsTo_tube (show (1 / 4 : ℝ) ≤ 1 by norm_num) b).2 y.property)
  · intro x hx hxB
    have hstrip (b : Bool) (hb : (x : P2) ∈ c b '' source) : False := by
      have hcenter := (original_strip_double_trace c hcS hdis hτ h0 h1 hfull b).subset ⟨hb, hx⟩
      exact disjoint_left.mp (E.center_disjoint_retainedSource hci b) hcenter x.property
    exact hxB.elim (hstrip false) (hstrip true)
  · exact hnew

end PoincareConjecture.M76.Dehn.NonspanningStripExteriors
