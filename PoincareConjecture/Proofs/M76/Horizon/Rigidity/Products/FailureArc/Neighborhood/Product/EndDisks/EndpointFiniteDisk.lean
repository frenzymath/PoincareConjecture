import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.NeighborhoodEuler
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.Purity.SurfaceSubdivision
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.Outward.EndpointFrontier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.ConnectedEndComplement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.FiniteDisk



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution ProductPieces
open BoundaryAssembly

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

theorem exists_original_endpoint_finite_disk
    {E X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {r w : ℝ} (hw : 0 < w) (hr1 : r < 1)
    {j : Bool → V2 → X}
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
    (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ)
    (hρ : ∀ b, 0 < ρ b) (hρr : ∀ b, ρ b < r) (hwρ : ∀ b, w / ρ b ≤ 1)
    (hmark : ∀ b, ∀ z ∈ Rim, ∀ s ∈ J,
      (P b).map (z,s) = F b (z,(w / ρ b)*s))
    (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F side (rimArmPoint b t,s) = prescribedArmBand U r (ρ side) 0 1 side b (s,t))
    (hlateral : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
      F side (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    (hdis : Disjoint ((P false).map '' (Disk ×ˢ J)) ((P true).map '' (Disk ×ˢ J)))
    (hopen : ∀ b v, 0 < v → v ≤ 1 →
      IsOpen ((Subtype.val : ↥(R \ U.map '' openTube r) → X) ⁻¹'
        ((P b).map '' (Disk ×ˢ Ioo (-v) v))))
    (hdistinct : connectedComponentIn (frontier R) (U.map ((0,0),0)) ≠
      connectedComponentIn (frontier R) (U.map ((0,0),1)))
    (t : I) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    (hKcount : K.surfaceEulerCount = 0)
    (H : K.space ≃ₜ connectedComponentIn (frontier R) (U.map ((0,0),t)))
    (a : E → X) (ha : PolyhedralPLInCharts e a K.space)
    (haval : ∀ x : K.space, a x = (H x : X)) :
    ∃ B L : SimplicialComplex ℝ E, B.faces.Finite ∧ L ≤ B ∧
      IsFinitePLBallPair P2 B.space L.space ∧
      PolyhedralPLInCharts e a B.space ∧ InjOn a B.space ∧
      a '' B.space = connectedComponentIn (frontier R) (U.map ((0,0),t)) \
        removedLongitudinalSlice U r P t ∧
      a '' L.space = ⋃ i, panelFamily U (P false) (P true) r w i '' (I ×ˢ {(t : ℝ)}) := by
  classical
  have hclosed (b : Bool) : (P b).closedStrip ⊆ (P b).map '' (Disk ×ˢ J) := by
    apply image_mono
    intro z hz
    exact ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
  have hdis' := hdis.mono (hclosed false) (hclosed true)
  obtain ⟨M,N,hM,hMK,hNM,hNs,_,hNcount⟩ :=
    exists_original_endpoint_neighborhood_euler_model U hR he hcompat hw hr1.le
      P F ρ hρ hρr hwρ hmark harms hlateral hdis' t ht K hK H a ha haval
  obtain ⟨hpureM,hcofacesM,hlinksM⟩ := hMK.closed_surface_incidence hK hM hpure hcofaces hlinks
  have hboundK (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ 3 := by
    obtain ⟨u,_,hu,hsu⟩ := hpure s hs
    exact (Finset.card_le_card hsu).trans_eq hu
  have hboundM (s : Finset E) (hs : s ∈ M.faces) : s.card ≤ 3 := by
    obtain ⟨u,_,hu,hsu⟩ := hpureM s hs
    exact (Finset.card_le_card hsu).trans_eq hu
  have hMcount : M.surfaceEulerCount = 0 :=
    (M.surfaceEulerCount_eq_of_space_eq K hM hK hboundM hboundK hMK.space_eq).trans hKcount
  let Z := connectedComponentIn (frontier R) (U.map ((0,0),t))
  let O : Set Z := (Subtype.val : Z → X) ⁻¹' removedLongitudinalSlice U r P t
  let H' : M.space ≃ₜ Z := (Homeomorph.setCongr hMK.space_eq).trans H
  have haM : PolyhedralPLInCharts e a M.space := hMK.space_eq.symm ▸ ha
  have haMv (x : M.space) : a x = (H' x : X) := haval ⟨x,hMK.space_eq.subset x.property⟩
  have hNs' : N.space = M.space ∩ a ⁻¹'
      (⋃ i, range (fun z => pieceParameter U P r i (z,t))) := by
    rw [hMK.space_eq]
    exact hNs
  obtain ⟨hO,hclosure,hinterior,hfrontier,_⟩ := endpoint_neighborhood_regular_open
    U hR he hw hr1 P F ρ hρ hρr hwρ hmark harms hlateral hdis hopen hdistinct t ht
  have himage : (Subtype.val : Z → X) '' Oᶜ = Z \ removedLongitudinalSlice U r P t := by
    ext x
    exact ⟨fun ⟨z,hz,heq⟩ => heq ▸ ⟨z.property,hz⟩,
      fun hx => ⟨⟨x,hx.1⟩,hx.2,rfl⟩⟩
  have hconn := isConnected_endpoint_complement U hR he hw hr1 P F ρ hρ hρr hwρ
    hmark harms hlateral hdis hopen hdistinct t ht
  rw [← himage] at hconn
  have hconn' : IsConnected Oᶜ :=
    ⟨Set.image_nonempty.mp hconn.nonempty,IsInducing.subtypeVal.isPreconnected_image.mp hconn.isPreconnected⟩
  obtain ⟨c,γ,hc,hci,_,hγ,hcA⟩ := exists_original_panel_end_rim U hR he hw hr1.le
    P F ρ hρ hρr hwρ hmark harms hlateral hdis' t ht
  have hcZ : MapsTo c Rim Z := fun z hz => (hγ ⟨z,hz⟩) ▸ (γ ⟨z,hz⟩).property
  obtain ⟨hball,hapl,hai,haimage,harim,_⟩ := original_model_complementary_disk hcompat
    M N hM hNM hpureM hcofacesM hlinksM hMcount hNcount H' a haM haMv O hO hconn'
    hNs' hclosure (by rw [hclosure]; exact hinterior)
    (by rw [hclosure]; exact hfrontier) c hc hci hcZ hcA
  exact ⟨M.closedFaceComplement N,N ⊓ M.closedFaceComplement N,
    M.closedFaceComplement_finite N hM,inf_le_right,hball,hapl,hai,
    haimage.trans himage,harim⟩

end PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
