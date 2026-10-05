import PoincareLib.Topology.Manifold.Smoothing.Dehn.DoubleCurve.Components.RetainedPartnerPL

/-!
# Finite PL partners on the two actual normalized disks

Both retained component families and their finite triangulations are
derived from the original strip geometry. The resulting partner acts
on the entire literal double locus of each constructed candidate.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

/-- Each actual candidate has a constructed finite PL, fixed-point-free
partner involution; every distinct equal-target source pair is its pair. -/
theorem OriginalNormalizedResolutionPairData.exists_finitePL_partners
    {F X ι I : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]
    [Finite I] {e : ι → OpenPartialHomeomorph X F}
    {f : V2 → X} {Z : Set X} {base : Z} {G : Subgroup (FundamentalGroup Z base)}
    {c : Bool → P2 → V2} {τ : C3 → X}
    {D : OriginalResolutionWordExclusionData f Z base G c τ (1 / 4)}
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
    (p : doubleLocusOn f D2 ≃ₜ doubleLocusOn f D2)
    (hpPL : p.IsFinitePL) (hp : Function.Involutive p)
    (hvalue : ∀ x, f (p x) = f x) (hfree : ∀ x, (p x : V2) ≠ x)
    (hrim : ∀ x, (p x : V2) ∈ Q2 ↔ (x : V2) ∈ Q2)
    (hunique : ∀ (x : doubleLocusOn f D2) (y : V2), y ∈ D2 →
      f x = f y → (x : V2) ≠ y → y = (p x : V2))
    (hcover : ⋃ i, U i = doubleLocusOn f D2)
    (hconn : ∀ i, IsConnected (U i))
    (hpairwise : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (hmodel : ∀ i, HasRetainedComponentModel (U i))
    (hmate : ∀ (i : I) (x : doubleLocusOn f D2),
      (x : V2) ∈ U i → (p x : V2) ∈ U (mate i))
    (a b : I) (ha : U a = c false '' arm 0) (hb : U b = c true '' arm 0) :
    ∀ g : V2 → X, g = P.gU ∨ g = P.gV →
      ∃ q : doubleLocusOn g D2 ≃ₜ doubleLocusOn g D2,
        q.IsFinitePL ∧ q.symm.IsFinitePL ∧ Function.Involutive q ∧
        (∀ x, g (q x) = g x) ∧ (∀ x, (q x : V2) ≠ x) ∧
        (∀ x, (q x : V2) ∈ Q2 ↔ (x : V2) ∈ Q2) ∧
        (∀ (x : doubleLocusOn g D2) (y : V2), y ∈ D2 →
          g x = g y → (x : V2) ≠ y → y = (q x : V2)) := by
  obtain ⟨factsU, factsV⟩ := P.retained_fibers hτ hfull h0 h1 hfZ
  obtain ⟨hPLU, hPLV⟩ := P.retained_finitePL_extensions
  obtain ⟨hwholeU, hwholeV, _⟩ := D.whole_double_components hci hcS hcQ hdisj
    hτ hfull h0 h1 U a b hcover hconn hpairwise ha hb
  have hLU := retained_double_locus_finitePL_id factsU.old_subset U mate p hcover hmodel
    (fun x ↦ (hvalue x).symm) (fun x ↦ Ne.symm (hfree x)) hunique hmate hwholeU
  have hLV := retained_double_locus_finitePL_id factsV.old_subset U mate p hcover hmodel
    (fun x ↦ (hvalue x).symm) (fun x ↦ Ne.symm (hfree x)) hunique hmate hwholeV
  intro g hg
  rcases hg with rfl | rfl
  · exact factsU.exists_finitePL_partner (D.diskA.isCompact.union D.diskC.isCompact)
      hPLU hLU p hpPL hp hvalue hfree hrim hunique
  · exact factsV.exists_finitePL_partner
      ((D.diskA.isCompact.union D.diskM.isCompact).union D.diskC.isCompact)
      hPLV hLV p hpPL hp hvalue hfree hrim hunique

end PoincareMT.M76.Dehn.PolygonalCrossingResolution
