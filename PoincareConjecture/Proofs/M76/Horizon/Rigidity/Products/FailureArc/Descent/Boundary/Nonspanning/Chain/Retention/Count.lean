import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Selection.Retention
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Retention.Relation
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedCounts

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.NonspanningStripExteriors

open PolygonalCrossingResolution NonspanningChainHole Annuli

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Rim" => Set.ofPred (fun x : P2 => depth 8 x = -1 ∨ depth 8 x = 1)

theorem boundary_count_decrease
    {X ι : Type*} [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V3}
    {c : Bool → P2 → P2} {D T : Set P2} (E : NonspanningStripExteriors c D T)
    (N : NonspanningChainAnnulus E.hole)
    (hD : IsFinitePLBallPair P2 D (frontier D))
    {f g : P2 → X} {τ : C3 → X} {Q : Set P2} {R : Set X}
    (K : SourceDoubleComponents e f (T \ interior D) Q R)
    (hfproper : ∀ x ∈ T \ interior D, f x ∈ frontier R ↔ x ∈ Q)
    (hci : ∀ j, InjOn (c j) source)
    (hcS : ∀ j, MapsTo (c j) source (T \ interior D))
    (hdis : Disjoint (c false '' source) (c true '' source)) (hτ : InjOn τ tube)
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfull : (T \ interior D) ∩ f ⁻¹' (τ '' tube) = c false '' source ∪ c true '' source)
    (selected : Bool → K.Index) (hcenter : ∀ j, c j '' arm 0 = K.pieces (selected j))
    (hmeet : (K.pieces (selected false) ∩ Q).Nonempty)
    (hproper : ∀ x ∈ Ann, g x ∈ frontier R ↔ x ∈ Rim)
    (hkeep : ∀ i (x : E.hole.sourceSet i), g (N.copy i x) =
      pieceMap f (τ ∘ tubeArmOrientation E.s0 E.s1) i x) :
    doubleBoundaryComponentCount g Ann Rim < doubleBoundaryComponentCount f (T \ interior D) Q ∧
      doubleInteriorComponentCount g Ann Rim ≤ doubleInteriorComponentCount f (T \ interior D) Q := by
  let j := N.retainedCopy E.disjoint_first_middle E.disjoint_first_last E.disjoint_middle_last
  have hji : Function.Injective j :=
    N.retainedCopy_injective E.disjoint_first_middle E.disjoint_first_last E.disjoint_middle_last
  obtain ⟨j', hj', hj'val⟩ := N.retainedCopy_PL E.disjoint_first_middle E.disjoint_first_last
    E.disjoint_middle_last E.retained_ball hD
  have hj : Continuous j := hj'.continuousOn.domRestrict.congr hj'val
  have hτ' : InjOn (τ ∘ tubeArmOrientation E.s0 E.s1) tube := by
    intro x hx y hy heq
    exact tubeArmOrientation_injective E.s0 E.s1
      (hτ ((tubeArmOrientation_mem_tube E.s0 E.s1 x).mpr hx)
        ((tubeArmOrientation_mem_tube E.s0 E.s1 y).mpr hy) heq)
  obtain ⟨hAtube, hMtube, hCtube⟩ := E.oriented_tube_preimages hfull
  have hcorners := E.oriented_corner_equations h0 h1
  obtain ⟨_, hlocus⟩ := N.retained_double_relation E.disjoint_first_middle E.disjoint_first_last
    E.disjoint_middle_last hkeep hτ' hAtube hMtube hCtube (fun t ↦ (hcorners t).1)
      (fun t ↦ (hcorners t).2.1) (fun t ↦ (hcorners t).2.2.1)
      (fun t ↦ (hcorners t).2.2.2)
  obtain ⟨hwhole, hremoved, _⟩ := E.whole_component_retention K hci hcS hdis hτ h0 h1
    hfull selected hcenter
  have hmark (x : N.retainedSet) : j x ∈ Rim ↔ (x : P2) ∈ Q := by
    have hjAnn : j x ∈ Ann := (N.retainedCopy_cover E.disjoint_first_middle
      E.disjoint_first_last E.disjoint_middle_last).subset (Or.inl ⟨x, rfl⟩)
    rw [← hproper _ hjAnn,
      N.retainedCopy_values E.disjoint_first_middle E.disjoint_first_last E.disjoint_middle_last hkeep]
    exact hfproper x (E.retainedSource_subset x.property)
  exact retained_double_component_counts_decrease K.pieces K.mate K.literalPartner rfl
    (K.cover.symm.trans K.space) K.compact K.connected K.disjoint K.literalPartner_value
    K.literalPartner_free K.literalPartner_unique K.literalPartner_component E.retainedSource_subset
    hwhole j hji hj hlocus hmark (selected false) hmeet (hremoved false).2

end PoincareConjecture.M76.Dehn.NonspanningStripExteriors
