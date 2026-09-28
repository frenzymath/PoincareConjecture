import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Selection.OpenCopy
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.CrossingFamily
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.Compactness
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.LocalInjectivity
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Reduction.SourceGeometry

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.NonspanningStripExteriors

open PolygonalCrossingResolution NonspanningChainHole Annuli

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem preserves_ordinary_crossings
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    {c : Bool → P2 → P2} {D T : Set P2} (E : NonspanningStripExteriors c D T)
    (N : NonspanningChainAnnulus E.hole)
    (hT : IsCompact T) (hD : IsFinitePLBallPair P2 D (frontier D))
    {f g : P2 → X} {τ : C3 → X} {Q : Set P2} {R : Set X}
    (K : SourceDoubleComponents e f (T \ interior D) Q R)
    (hf : ContinuousOn f (T \ interior D)) (hg : ContinuousOn g Ann)
    (hc : ∀ j, ContinuousOn (c j) source) (hci : ∀ j, InjOn (c j) source)
    (hcS : ∀ j, MapsTo (c j) source (T \ interior D))
    (hdis : Disjoint (c false '' source) (c true '' source)) (hτ : InjOn τ tube)
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfull : (T \ interior D) ∩ f ⁻¹' (τ '' tube) = c false '' source ∪ c true '' source)
    (hkeep : ∀ i (x : E.hole.sourceSet i), g (N.copy i x) =
      pieceMap f (τ ∘ tubeArmOrientation E.s0 E.s1) i x) :
    IsCompact (doubleLocusOn g Ann) ∧
      (∀ x ∈ Ann, ∀ y ∈ Ann, ∀ z ∈ Ann,
        x ≠ y → x ≠ z → g x = g y → g x = g z → y = z) ∧
      (∀ x ∈ Ann, ∀ y ∈ Ann, x ≠ y → g x = g y →
        Nonempty (RawSourceCrossing e g Ann R x y)) ∧
      IsLocallyInjective (fun x : Ann ↦ g x) := by
  let j := N.retainedCopy E.disjoint_first_middle E.disjoint_first_last E.disjoint_middle_last
  have hji : Function.Injective j :=
    N.retainedCopy_injective E.disjoint_first_middle E.disjoint_first_last E.disjoint_middle_last
  obtain ⟨j', hj', hj'val⟩ := N.retainedCopy_PL E.disjoint_first_middle E.disjoint_first_last
    E.disjoint_middle_last E.retained_ball hD
  have hj : Continuous j := hj'.continuousOn.domRestrict.congr hj'val
  have hK : IsCompact N.retainedSet :=
    ((E.first_ball.isCompact.diff isOpen_interior).union
      (E.middle_ball.isCompact.diff isOpen_interior)).union
        (E.last_ball.isCompact.diff isOpen_interior)
  have hτ' : InjOn (τ ∘ tubeArmOrientation E.s0 E.s1) tube := by
    intro x hx y hy heq
    exact tubeArmOrientation_injective E.s0 E.s1
      (hτ ((tubeArmOrientation_mem_tube E.s0 E.s1 x).mpr hx)
        ((tubeArmOrientation_mem_tube E.s0 E.s1 y).mpr hy) heq)
  obtain ⟨hAtube, hMtube, hCtube⟩ := E.oriented_tube_preimages hfull
  have hcorners := E.oriented_corner_equations h0 h1
  obtain ⟨hrel, hlocus⟩ := N.retained_double_relation E.disjoint_first_middle E.disjoint_first_last
    E.disjoint_middle_last hkeep hτ' hAtube hMtube hCtube (fun t ↦ (hcorners t).1)
      (fun t ↦ (hcorners t).2.1) (fun t ↦ (hcorners t).2.2.1)
      (fun t ↦ (hcorners t).2.2.2)
  have hG : IsCompact (doubleLocusOn f (T \ interior D)) :=
    K.space ▸ K.graph.isCompact_space_of_finite K.finite
  have hcompact : IsCompact (doubleLocusOn g Ann) :=
    isCompact_new_double_locus_of_retained E.retainedSource_subset hK.isClosed hG
      K.literalPartner K.literalPartner.continuous (fun x ↦ (K.literalPartner_value x).symm)
      (fun x ↦ (K.literalPartner_free x).symm) K.literalPartner_unique j hj hlocus
  have hraw : ∀ x ∈ Ann, ∀ y ∈ Ann, x ≠ y → g x = g y →
      Nonempty (RawSourceCrossing e g Ann R x y) := by
    obtain ⟨U, V, H, hUK, hVAnn, hU, hV, _, hvalues, _, hcontains⟩ :=
      E.exists_retained_open_copy N hD hc hci hcS hdis hτ h0 h1 hfull hkeep
    have hh := raw_source_crossings_of_retained_open_copy (hT.diff isOpen_interior)
      isCompact_planar_annulus (hUK.trans E.retainedSource_subset) hVAnn hU hV hf hg H
      hvalues K.literalPartner K.literalPartner_unique hcontains
      (fun x hx y hy hxy hne ↦ K.crossings x hx y hy hne hxy)
    exact fun x hx y hy hne hxy ↦ hh x hx y hy hxy hne
  refine ⟨hcompact, ?_, hraw, isLocallyInjective_of_raw_source_crossings hcompact.isClosed hraw⟩
  intro x hx y hy z hz hxy hxz hfv hfw
  apply retained_relation_unique_other_point E.retainedSource_subset j hji hrel ?_
    x y z hx hy hz hfv hfw hxy hxz
  intro a ha b hb d hd hab had hnab hnad
  let u : doubleLocusOn f (T \ interior D) := ⟨a, ha, b, hb, hab, hnab⟩
  exact (K.literalPartner_unique u b hb hab hnab).trans
    (K.literalPartner_unique u d hd had hnad).symm

end PoincareConjecture.M76.Dehn.NonspanningStripExteriors
