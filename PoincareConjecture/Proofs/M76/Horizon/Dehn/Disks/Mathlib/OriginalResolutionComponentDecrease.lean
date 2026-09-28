import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.OriginalNormalizedResolutionFibers
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.OriginalResolution
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedCounts

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem OriginalNormalizedResolutionPairData.component_counts_decrease
    {F X ι I : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace X] [Finite I] {e : ι → OpenPartialHomeomorph X F}
    {f : V2 → X} {Z : Set X} {base : Z} {H : Subgroup (FundamentalGroup Z base)}
    {c : Bool → P2 → V2} {τ : C3 → X}
    {D : OriginalResolutionWordExclusionData f Z base H c τ (1 / 4)}
    (P : OriginalNormalizedResolutionPairData e D)
    (hci : ∀ i, InjOn (c i) source) (hcS : ∀ i, MapsTo (c i) source D2)
    (hcQ : ∀ i p, p ∈ source → (c i p ∈ Q2 ↔ p.1 = 0 ∨ p.1 = 1))
    (hdisj : Disjoint (c false '' source) (c true '' source))
    (hτ : InjOn τ tube)
    (hfull : D2 ∩ f ⁻¹' (τ '' tube) = (c false '' source) ∪ (c true '' source))
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfZ : ∀ x ∈ D2, f x ∈ Z ↔ x ∈ Q2)
    (U : I → Set V2) (mate : I → I)
    (partner : doubleLocusOn f D2 → doubleLocusOn f D2)
    (hcover : ⋃ i, U i = doubleLocusOn f D2)
    (hcompact : ∀ i, IsCompact (U i)) (hconn : ∀ i, IsConnected (U i))
    (hpairwise : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (hpartner : ∀ x : doubleLocusOn f D2, f x = f (partner x))
    (hne : ∀ x : doubleLocusOn f D2, (x : V2) ≠ partner x)
    (hunique : ∀ (x : doubleLocusOn f D2) (y : V2), y ∈ D2 →
      f x = f y → (x : V2) ≠ y → y = (partner x : V2))
    (hmate : ∀ (i : I) (x : doubleLocusOn f D2),
      (x : V2) ∈ U i → (partner x : V2) ∈ U (mate i))
    (a b : I) (ha : U a = c false '' arm 0) (hb : U b = c true '' arm 0) :
    (doubleBoundaryComponentCount P.gU D2 Q2 < doubleBoundaryComponentCount f D2 Q2 ∧
      doubleInteriorComponentCount P.gU D2 Q2 ≤ doubleInteriorComponentCount f D2 Q2) ∧
    (doubleBoundaryComponentCount P.gV D2 Q2 < doubleBoundaryComponentCount f D2 Q2 ∧
      doubleInteriorComponentCount P.gV D2 Q2 ≤ doubleInteriorComponentCount f D2 Q2) := by
  obtain ⟨hwholeU, hwholeV, hiQ, hnotU, hnotV⟩ := D.whole_double_components
    hci hcS hcQ hdisj hτ hfull h0 h1 U a b hcover hconn hpairwise ha hb
  obtain ⟨factsU, factsV⟩ := P.retained_fibers hτ hfull h0 h1 hfZ
  have hcount (g : V2 → X) (K : Set V2) (j : K → V2)
      (facts : RetainedSquareMapFacts f g K j)
      (hwhole : ∀ i, U i ⊆ K ∨ Disjoint (U i) K) (hnot : ¬ U a ⊆ K) :
      doubleBoundaryComponentCount g D2 Q2 < doubleBoundaryComponentCount f D2 Q2 ∧
        doubleInteriorComponentCount g D2 Q2 ≤ doubleInteriorComponentCount f D2 Q2 := by
    exact retained_double_component_counts_decrease U mate partner rfl hcover
      hcompact hconn hpairwise hpartner hne hunique hmate facts.old_subset hwhole j
      facts.injective facts.continuous facts.double_locus facts.boundary a hiQ hnot
  exact ⟨hcount P.gU _ P.retainedUpperCopy factsU hwholeU hnotU,
    hcount P.gV _ P.retainedAlternateCopy factsV hwholeV hnotV⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
