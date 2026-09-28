import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Reduction.Neighborhood
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.OrientedSpanningTube



set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli.ProductConstruction
open PolygonalCrossingResolution
open Poincare.Topology.Orientation.ProjectivePlane

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "I" => Icc (0 : ℝ) 1
local notation "Last" => Set.ofPred (fun x : P2 => depth 8 x = 1)

open Classical in
theorem exists_marked_product_of_positioned_annulus_pair_of_localOrientation
    {X ι : Type} [TopologicalSpace X] [T2Space X]
    (O : LocalOrientation X)
    (E : Bool → Type) [∀ b, NormedAddCommGroup (E b)]
    [∀ b, NormedSpace ℝ (E b)] [∀ b, FiniteDimensional ℝ (E b)]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (F : Bool → Set X)
    (hR : IsCompact R) (hI : IsPLIrreducible e R) (hconn : IsPreconnected R)
    (hF : ∀ b, F b ⊆ frontier R)
    (hFopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' F true))
    (hFdis : Disjoint (F false) (F true))
    (hcomponent : ∀ b y, y ∈ F b → connectedComponentIn (frontier R) y = F b)
    (K : ∀ b, SimplicialComplex ℝ (E b)) (hK : ∀ b, (K b).faces.Finite)
    (hpure : ∀ b, ∀ s ∈ (K b).faces, ∃ t ∈ (K b).faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ b, ∀ s ∈ (K b).faces, s.card = 2 →
      {t : Finset (E b) | t ∈ (K b).faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ b, ∀ q ∈ (K b).vertices, IsConnected ((K b).link q).space)
    (hcount : ∀ b, (K b).surfaceEulerCount = 0)
    (Hmodel : ∀ b, (K b).space ≃ₜ F b)
    (a : ∀ b, E b → X) (ha : ∀ b, PolyhedralPLInCharts e (a b) (K b).space)
    (hav : ∀ b, ∀ z : (K b).space, a b z = (Hmodel b z : X))
    {f g : P2 → X}
    (hf : PolyhedralPLInCharts e f Ann) (hg : PolyhedralPLInCharts e g Ann)
    (hfi : InjOn f Ann) (hgi : InjOn g Ann)
    (hfR : MapsTo f Ann R) (hgR : MapsTo g Ann R)
    (hfp : ∀ x ∈ Ann, f x ∈ frontier R ↔ x ∈ frontier Ann)
    (hgp : ∀ x ∈ Ann, g x ∈ frontier R ↔ x ∈ frontier Ann)
    (hfmark : ∀ x ∈ Ann, f x ∈ F false ↔ depth 8 x = -1)
    (hgmark : ∀ x ∈ Ann, g x ∈ F false ↔ depth 8 x = -1)
    (hflast : MapsTo f (Ann ∩ Last) (F true))
    (hglast : MapsTo g (Ann ∩ Last) (F true))
    (p : X) (hpoint : ((f '' Ann) ∩ (g '' Ann)) ∩ F false = {p})
    (hboundary : ∀ x ∈ Ann ∩ frontier Ann, f x ∈ g '' Ann →
      ∃ B : OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) true,
        (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0)
    (hinterior : ∀ x ∈ Ann \ frontier Ann, f x ∈ g '' Ann →
      Nonempty (OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) false)) :
    ∃ H : ((F false) × I) ≃ₜ R,
      (∀ x, (H (x,⟨0,by norm_num⟩) : X) = x) ∧
      range (fun x => (H (x,⟨1,by norm_num⟩) : X)) = F true ∧
      (∀ x t, (H (x,t) : X) ∈ frontier R ↔ (t : ℝ) = 0 ∨ (t : ℝ) = 1) ∧
      ∃ (s : Finset R) (G : X → (s → ℝ × V3))
        (HG : ((G '' F false) ×ˢ I) ≃ₜ (G '' R)),
        Continuous G ∧
        (∀ i, LocallyPiecewiseAffineOn (G ∘ (e i).symm) (e i).target) ∧
        (∀ x ∈ R, ∀ y : X, G x = G y → x = y) ∧
        HG.IsFinitePL ∧ HG.symm.IsFinitePL ∧
        (∀ (x : F false) (t : I),
          (HG ⟨(G x,t),⟨mem_image_of_mem G x.property,t.property⟩⟩ : s → ℝ × V3) =
            G (H (x,t))) ∧
        ∀ x ∈ R, ∃ (i : ι) (V : Set X) (b : (s → ℝ × V3) →ᴬ[ℝ] V3),
          IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (b ∘ G) (e i) V := by
  classical
  obtain ⟨k,hk,hki,hkR,hkp,V,hv0,hv1,hs00,hs01,hs10,hs11⟩ :=
    exists_original_reduced_marked_tube_of_hausdorff (W := univ) F hR hI.1
      hF hFopen hFdis hf hg hfi hgi hfR hgR hfp hgp hfmark hgmark hflast hglast
      p hpoint hboundary hinterior isOpen_univ (subset_univ _)
  have hki' : InjOn k Ann := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hki.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) hxy)
  have hsource0 : (0,0) ∈ source := by norm_num [source]
  have hsource1 : (1,0) ∈ source := by norm_num [source]
  have harm0 : (0,0) ∈ arm 0 := by norm_num [arm]
  have harm1 : (1,0) ∈ arm 0 := by norm_num [arm]
  have houter₀ : ((Ann ∩ g ⁻¹' (k '' Ann)) ∩ {z : P2 | depth 8 z = -1}).Nonempty :=
    ⟨V.first (0,0),V.first_center.subset (mem_image_of_mem V.first harm0),
      (hs00 _ hsource0).mpr rfl⟩
  have hinner₀ : ((Ann ∩ g ⁻¹' (k '' Ann)) ∩ {z : P2 | depth 8 z = 1}).Nonempty :=
    ⟨V.first (1,0),V.first_center.subset (mem_image_of_mem V.first harm1),
      (hs01 _ hsource1).mpr rfl⟩
  have houter₁ : ((Ann ∩ k ⁻¹' (g '' Ann)) ∩ {z : P2 | depth 8 z = -1}).Nonempty :=
    ⟨V.second (0,0),V.second_center.subset (mem_image_of_mem V.second harm0),
      (hs10 _ hsource0).mpr rfl⟩
  have hinner₁ : ((Ann ∩ k ⁻¹' (g '' Ann)) ∩ {z : P2 | depth 8 z = 1}).Nonempty :=
    ⟨V.second (1,0),V.second_center.subset (mem_image_of_mem V.second harm1),
      (hs11 _ hsource1).mpr rfl⟩
  have hpF : p ∈ F false := (hpoint.symm.subset (mem_singleton p)).2
  have hanchor (b : Bool) : V.map ((0,0),if b then 1 else 0) ∈ F b := by
    cases b
    · simpa only [Bool.false_eq_true,if_false,hv0] using hpF
    · exact hv1
  have hZ (b : Bool) : connectedComponentIn (frontier R)
      (V.map ((0,0),if b then 1 else 0)) = F b :=
    hcomponent b _ (hanchor b)
  have hZ0 : connectedComponentIn (frontier R) (V.map ((0,0),0)) = F false := hZ false
  have hZ1 : connectedComponentIn (frontier R) (V.map ((0,0),1)) = F true := hZ true
  have hdistinct : connectedComponentIn (frontier R) (V.map ((0,0),0)) ≠
      connectedComponentIn (frontier R) (V.map ((0,0),1)) := by
    rw [hZ0,hZ1]
    intro h
    exact disjoint_left.mp hFdis hpF (h ▸ hpF)
  let H (b : Bool) : (K b).space ≃ₜ
      connectedComponentIn (frontier R) (V.map ((0,0),if b then 1 else 0)) :=
    (Hmodel b).trans (Homeomorph.setCongr (hZ b).symm)
  have hproduct := exists_marked_product_of_spanning_tube_of_localOrientation O E
    V hR hI hconn hg hk hgi hki' hgR hkR hgp hkp
    houter₀ hinner₀ houter₁ hinner₁ rfl hdistinct K hK hpure hcofaces hlinks hcount
    H a ha (fun b z => hav b z)
  dsimp only at hproduct
  rw [hZ0,hZ1] at hproduct
  exact hproduct

end PoincareConjecture.M76.Dehn.Annuli.ProductConstruction
