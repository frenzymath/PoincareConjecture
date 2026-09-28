import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Reduction.TubeConstruction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Reduction.OrientedTube



set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Src" => PolygonalCrossingResolution.source
local notation "First" => Set.ofPred (fun x : P2 => depth 8 x = -1)
local notation "Last" => Set.ofPred (fun x : P2 => depth 8 x = 1)

theorem exists_original_reduced_annulus_with_marked_interval_tube
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X} (F : Bool → Set X)
    (hR : IsCompact R) (he : PLDomain e R) (hF : ∀ b, F b ⊆ frontier R)
    (hFopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' F true))
    (hFdis : Disjoint (F false) (F true)) {f g : P2 → X}
    (hf : PolyhedralPLInCharts e f Ann) (hg : PolyhedralPLInCharts e g Ann)
    (hfi : InjOn f Ann) (hgi : InjOn g Ann) (hfR : MapsTo f Ann R) (hgR : MapsTo g Ann R)
    (hfp : ∀ x ∈ Ann, f x ∈ frontier R ↔ x ∈ frontier Ann)
    (hgp : ∀ x ∈ Ann, g x ∈ frontier R ↔ x ∈ frontier Ann)
    (hfmark : ∀ x ∈ Ann, f x ∈ F false ↔ depth 8 x = -1)
    (hgmark : ∀ x ∈ Ann, g x ∈ F false ↔ depth 8 x = -1)
    (hflast : MapsTo f (Ann ∩ Last) (F true)) (hglast : MapsTo g (Ann ∩ Last) (F true))
    (p : X) (hpoint : ((f '' Ann) ∩ (g '' Ann)) ∩ F false = {p})
    (hboundary : ∀ x ∈ Ann ∩ frontier Ann, f x ∈ g '' Ann →
      ∃ B : OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) true,
        (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0)
    (hinterior : ∀ x ∈ Ann \ frontier Ann, f x ∈ g '' Ann →
      Nonempty (OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) false))
    (hW : IsOpen W) (hCW : f '' Ann ∩ g '' Ann ⊆ W) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k Ann ∧ IsEmbedding (fun x : Ann ↦ k x) ∧
      MapsTo k Ann R ∧ EqOn k f (Ann ∩ First) ∧ MapsTo k (Ann ∩ Last) (F true) ∧
      (∀ x ∈ Ann, k x ∈ frontier R ↔ x ∈ frontier Ann) ∧
      (∀ x ∈ Ann, k x ∈ F false ↔ depth 8 x = -1) ∧
      ((k '' Ann) ∩ (g '' Ann)) ∩ F false = {p} ∧
      Ann ∩ k ⁻¹' (g '' Ann) ⊆ Ann ∩ f ⁻¹' (g '' Ann) ∧
      EqOn k f (Ann ∩ k ⁻¹' (g '' Ann)) ∧
      (∀ x ∈ Ann ∩ frontier Ann, k x ∈ g '' Ann →
        ∃ B : OriginalSurfacePairChart e (g '' Ann) (k '' Ann) (k x) true,
          (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
          ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0) ∧
      (∀ x ∈ Ann \ frontier Ann, k x ∈ g '' Ann →
        Nonempty (OriginalSurfacePairChart e (g '' Ann) (k '' Ann) (k x) false)) ∧
      IsFinitePLBallPair ℝ (Ann ∩ g ⁻¹' (k '' Ann))
        ((Ann ∩ g ⁻¹' (k '' Ann)) ∩ frontier Ann) ∧
      ∃ V : OriginalIntervalTube e R W Ann Ann
          (Ann ∩ g ⁻¹' (k '' Ann)) (Ann ∩ k ⁻¹' (g '' Ann)) g k,
        V.map ((0, 0), 0) = p ∧ V.map ((0, 0), 1) ∈ F true ∧
        (∀ t ∈ Icc (0 : ℝ) 1, V.map ((0, 0), t) ∈ F false ↔ t = 0) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, V.map ((0, 0), t) ∈ F true ↔ t = 1) ∧
        (∀ q ∈ Src, depth 8 (V.first q) = -1 ↔ q.1 = 0) ∧
        (∀ q ∈ Src, depth 8 (V.first q) = 1 ↔ q.1 = 1) ∧
        (∀ q ∈ Src, depth 8 (V.second q) = -1 ↔ q.1 = 0) ∧
        (∀ q ∈ Src, depth 8 (V.second q) = 1 ↔ q.1 = 1) ∧
        ∃ H : unitInterval ≃ₜ (Ann ∩ g ⁻¹' (k '' Ann) : Set P2),
          H.IsFinitePL ∧ H.symm.IsFinitePL ∧ g (H 0) = p ∧ g (H 1) ∈ F true ∧
          (∀ t : unitInterval, g (H t) ∈ frontier R ↔ t = 0 ∨ t = 1) ∧
          (∀ t : unitInterval, g (H t) ∈ F false ↔ t = 0) ∧
          Nat.card (ConnectedComponents (Ann ∩ g ⁻¹' (k '' Ann) : Set P2)) = 1 := by
  obtain ⟨k, hk, hki, hkR, hkfirst, hklast, hkp, hkmark, hkpoint, hksub, hkkeep,
    hkb, hkint, ⟨U⟩, hball, H, hH, hHi, h0, h1, hfront, hmark, hcount⟩ :=
    exists_original_reduced_annulus_with_whole_interval_tube F hR he hF hFopen hFdis
      hf hg hfi hgi hfR hgR hfp hgp hfmark hgmark hflast hglast p hpoint hboundary hinterior hW hCW
  have hlast : (((k '' Ann) ∩ (g '' Ann)) ∩ F true).Nonempty :=
    ⟨g (H 1), ⟨(H 1).property.2, H 1, (H 1).property.1, rfl⟩, h1⟩
  obtain ⟨V, hv0, hv1, hvfirst, hvlast, hs00, hs01, hs10, hs11⟩ :=
    U.exists_oriented_whole F hF hFdis hkp hgp hkmark hgmark hglast p hkpoint hlast
  exact ⟨k, hk, hki, hkR, hkfirst, hklast, hkp, hkmark, hkpoint, hksub, hkkeep,
    hkb, hkint, hball, V, hv0, hv1, hvfirst, hvlast, hs00, hs01, hs10, hs11,
    H, hH, hHi, h0, h1, hfront, hmark, hcount⟩

end PoincareConjecture.M76.Dehn.Annuli
