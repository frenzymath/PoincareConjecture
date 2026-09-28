import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.OrdinaryModel
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedPartnerPL
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedPairing
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Crossings.RetainedCrossings

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem RetainedSquareMapFacts.nonempty_ordinary_model
    {X ι : Type*} [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V3}
    {f g : V2 → X} {R : Set X} {K : Set V2} {j : K → V2}
    (facts : RetainedSquareMapFacts f g K j) (old : OrdinaryDoubleCurveModel e f R)
    (hK : IsCompact K)
    (hPL : ∃ J : V2 → V2, FinitePiecewiseAffineOn J K ∧ ∀ x : K, J x = j x)
    (hwhole : ∀ i, old.pieces i ⊆ K ∨ Disjoint (old.pieces i) K)
    (hcross : ∀ x ∈ D2, ∀ y ∈ D2, x ≠ y → g x = g y →
      Nonempty (RawCrossingChart e g R x y)) :
    Nonempty (OrdinaryDoubleCurveModel e g R) := by
  let : Finite old.Index := old.finiteIndex
  let I := {i // old.pieces i ⊆ K ∧ old.pieces (old.mate i) ⊆ K}
  let V (i : I) := j '' ((Subtype.val : K → V2) ⁻¹' old.pieces i.val)
  let mate := retainedComponentMate old.pieces K old.mate old.mate_involutive
  obtain ⟨hcover, hmodel, hcompact, hdisj⟩ := facts.component_model_partition hPL
    old.pieces old.mate old.partner old.cover old.compact old.connected old.disjoint old.models
    (fun x ↦ (old.partner_value x).symm) (fun x ↦ Ne.symm (old.partner_free x))
    old.unique_partner old.partner_component hwhole
  have hL := retained_double_locus_finitePL_id facts.old_subset old.pieces old.mate
    old.partner old.cover old.models (fun x ↦ (old.partner_value x).symm)
    (fun x ↦ Ne.symm (old.partner_free x)) old.unique_partner old.partner_component hwhole
  obtain ⟨q, hqPL, _, hq2, hqval, hqfree, hqrim, hqunique⟩ := facts.exists_finitePL_partner
    hK hPL hL old.partner old.partnerPL old.partner_involutive old.partner_value
    old.partner_free old.partner_rim old.unique_partner
  refine ⟨{
    Index := I
    finiteIndex := inferInstance
    pieces := V
    mate := mate
    mate_involutive := retainedComponentMate_involutive _ _ _ _
    cover := hcover
    compact := fun i ↦ (hcompact i).1
    connected := fun i ↦ (hcompact i).2
    disjoint := hdisj
    models := hmodel
    partner := q
    partnerPL := hqPL
    partner_involutive := hq2
    partner_value := hqval
    partner_free := hqfree
    partner_rim := hqrim
    unique_partner := hqunique
    partner_component := ?_
    crossings := hcross }⟩
  intro i x hx
  exact facts.partner_mem_component old.pieces old.mate old.cover old.partner
    old.partner_value old.partner_free old.partner_component q hqunique i.val i.property.2 x hx

theorem OriginalNormalizedResolutionPairData.nonempty_ordinary_models
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    {f : V2 → X} {Z R : Set X} {base : Z} {G : Subgroup (FundamentalGroup Z base)}
    {c : Bool → P2 → V2} {τ : C3 → X}
    {D : OriginalResolutionWordExclusionData f Z base G c τ (1 / 4)}
    (P : OriginalNormalizedResolutionPairData e D)
    (old : OrdinaryDoubleCurveModel e f R)
    (hf : ContinuousOn f D2) (hτc : ContinuousOn τ tube)
    (hcPL : ∀ i, FinitePiecewiseAffineOn (c i) source)
    (hci : ∀ i, InjOn (c i) source) (hcS : ∀ i, MapsTo (c i) source D2)
    (hcQ : ∀ i p, p ∈ source → (c i p ∈ Q2 ↔ p.1 = 0 ∨ p.1 = 1))
    (hdisj : Disjoint (c false '' source) (c true '' source))
    (hτ : InjOn τ tube)
    (hfull : D2 ∩ f ⁻¹' (τ '' tube) = (c false '' source) ∪ (c true '' source))
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfZ : ∀ x ∈ D2, f x ∈ Z ↔ x ∈ Q2)
    (a b : old.Index) (ha : old.pieces a = c false '' arm 0)
    (hb : old.pieces b = c true '' arm 0) :
    Nonempty (OrdinaryDoubleCurveModel e P.gU R) ∧
      Nonempty (OrdinaryDoubleCurveModel e P.gV R) := by
  obtain ⟨factsU, factsV⟩ := P.retained_fibers hτ hfull h0 h1 hfZ
  obtain ⟨hPLU, hPLV⟩ := P.retained_finitePL_extensions
  obtain ⟨hwholeU, hwholeV, _⟩ := D.whole_double_components hci hcS hcQ hdisj hτ hfull h0 h1
    old.pieces a b old.cover old.connected old.disjoint ha hb
  obtain ⟨hcrossU, hcrossV⟩ := P.exists_raw_crossing_charts hf hτc hcPL hci hcS hdisj hτ hfull
    h0 h1 hfZ old.partner old.unique_partner old.crossings
  exact ⟨factsU.nonempty_ordinary_model old (D.diskA.isCompact.union D.diskC.isCompact)
      hPLU hwholeU (fun x hx y hy hne hxy ↦ ⟨(hcrossU x hx y hy hne hxy).choose⟩),
    factsV.nonempty_ordinary_model old
      ((D.diskA.isCompact.union D.diskM.isCompact).union D.diskC.isCompact)
      hPLV hwholeV (fun x hx y hy hne hxy ↦ ⟨(hcrossV x hx y hy hne hxy).choose⟩)⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
