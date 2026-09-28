import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.FinalCutAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.FinalBallFromEndDisks
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.ActualAttachedPanelRim
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.Construction.CutBall
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Pieces.CompactBase
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.SliceImages
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Pieces.Filled
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.GraphProduct
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.WholeEnds
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.FinalBallFrontier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Pieces.OriginalFrontier



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductConstruction
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution
open ProductPieces BoundaryAssembly AnnularParameter

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "DiskV" => closedBall (0 : V2) 1
local notation "Disk" => closedBall (0 : P2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

theorem exists_whole_region_product_of_end_disks
    {X ι E₀ E₁ : Type} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (hI : IsPLIrreducible e R) (hconn : IsPreconnected R)
    {r w : ℝ} (hw : 0 < w) (hr1 : r < 1)
    {j : Bool → V2 → X}
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
    (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ)
    (hρ : ∀ b, 0 < ρ b) (hρr : ∀ b, ρ b < r) (hwρ : ∀ b, w/ρ b ≤ 1)
    (hmark : ∀ b, ∀ z ∈ Rim, ∀ s ∈ J,
      (P b).map (z,s) = F b (z,(w/ρ b)*s))
    (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F side (rimArmPoint b t,s) = prescribedArmBand U r (ρ side) 0 1 side b (s,t))
    (hlateral : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
      F side (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    (hdis : Disjoint ((P false).map '' (DiskV ×ˢ J)) ((P true).map '' (DiskV ×ˢ J)))
    (hopen : ∀ b, ∀ v : ℝ, 0 < v → v ≤ 1 →
      IsOpen ((Subtype.val : ↥(R \ U.map '' openTube r) → X) ⁻¹'
        ((P b).map '' (DiskV ×ˢ Ioo (-v) v))))
    {g₀ : E₀ → X} {g₁ : E₁ → X} {c₀ q₀ : Set E₀} {c₁ q₁ : Set E₁}
    (hc₀ : IsFinitePLBallPair P2 c₀ q₀) (hc₁ : IsFinitePLBallPair P2 c₁ q₁)
    (hg₀ : PolyhedralPLInCharts e g₀ c₀) (hg₁ : PolyhedralPLInCharts e g₁ c₁)
    (hi₀ : InjOn g₀ c₀) (hi₁ : InjOn g₁ c₁)
    (hrim₀ : (⋃ i, panelFamily U (P false) (P true) r w i '' (I ×ˢ {0})) = g₀ '' q₀)
    (hrim₁ : (⋃ i, panelFamily U (P false) (P true) r w i '' (I ×ˢ {1})) = g₁ '' q₁)
    (hcontact₀ : ((⋃ i : Bool × Bool, U.map '' panel r (w/2) i) ∪
      ((P false).endDisks ∪ (P true).endDisks)) ∩ (g₀ '' c₀) = g₀ '' q₀)
    (hcontact₁ : ((⋃ i : Bool × Bool, U.map '' panel r (w/2) i) ∪
      ((P false).endDisks ∪ (P true).endDisks)) ∩ (g₁ '' c₁) = g₁ '' q₁)
    (hgdis : Disjoint (g₀ '' c₀) (g₁ '' c₁))
    (hold₀ : g₀ '' c₀ ⊆ frontier R \
      (U.map '' openTube r ∪ (P false).openStrip ∪ (P true).openStrip))
    (hold₁ : g₁ '' c₁ ⊆ frontier R \
      (U.map '' openTube r ∪ (P false).openStrip ∪ (P true).openStrip)) :
    ∃ H : (((⋃ i, range (pieceBottom U P r i)) ∪ g₀ '' c₀ : Set X) × I) ≃ₜ R,
      (∀ x, (H (x, ⟨0, by norm_num⟩) : X) = x) ∧
      range (fun x => (H (x, ⟨1, by norm_num⟩) : X)) =
        (⋃ i, range (fun z => pieceParameter U P r i (z, ⟨1, by norm_num⟩))) ∪
          g₁ '' c₁ ∧
      (∀ i z t, (H (⟨pieceBottom U P r i z,
        Or.inl (mem_iUnion.mpr ⟨i, mem_range_self z⟩)⟩, t) : X) =
          pieceParameter U P r i (z, t)) ∧
      (∃ (k : P2 × ℝ → X)
        (q : Disk → ((⋃ i, range (pieceBottom U P r i)) ∪ g₀ '' c₀ : Set X)),
        PolyhedralPLInCharts e k (Disk ×ˢ I) ∧ InjOn k (Disk ×ˢ I) ∧
        (∀ z, (q z : X) = k (z, 0)) ∧ range (fun z => (q z : X)) = g₀ '' c₀ ∧
        ∀ z t, (H (q z, t) : X) = k (z, t)) ∧
      (∀ x t, (H (x, t) : X) ∈ frontier R ↔ (t : ℝ) = 0 ∨ (t : ℝ) = 1) ∧
      (∀ (x : ((⋃ i, range (pieceBottom U P r i)) ∪ g₀ '' c₀ : Set X)),
        connectedComponentIn (frontier R) (x : X) =
          ((⋃ i, range (pieceBottom U P r i)) ∪ g₀ '' c₀) ∧
        connectedComponentIn (frontier R) (H (x, ⟨1, by norm_num⟩) : X) =
          (⋃ i, range (fun z => pieceParameter U P r i (z, ⟨1, by norm_num⟩))) ∪ g₁ '' c₁) ∧
      ∃ (a : Finset R) (G : X → (a → ℝ × V3))
        (HG : ((G '' ((⋃ i, range (pieceBottom U P r i)) ∪ g₀ '' c₀)) ×ˢ I) ≃ₜ (G '' R)),
        Continuous G ∧
        (∀ i, LocallyPiecewiseAffineOn (G ∘ (e i).symm) (e i).target) ∧
        (∀ x ∈ R, ∀ y : X, G x = G y → x = y) ∧
        HG.IsFinitePL ∧ HG.symm.IsFinitePL ∧
        (∀ (x : ((⋃ i, range (pieceBottom U P r i)) ∪ g₀ '' c₀ : Set X)) (t : I),
          (HG ⟨(G x, t), ⟨mem_image_of_mem G x.property, t.property⟩⟩ :
          a → ℝ × V3) = G (H (x, t))) ∧
        ∀ x ∈ R, ∃ (i : ι) (V : Set X) (b : (a → ℝ × V3) →ᴬ[ℝ] V3),
          IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (b ∘ G) (e i) V := by
  classical
  obtain ⟨Q, hmap, _, hQc, _, hQfront, ⟨ball⟩⟩ :=
    nonempty_original_ball_of_marked_disk_products U hR hI hconn hw hr1 P F ρ
      hρ hρr hwρ hmark harms hlateral hdis hopen hc₀ hc₁ hg₀ hg₁ hi₀ hi₁
      hrim₀ hrim₁ hcontact₀ hcontact₁ hgdis hold₀ hold₁
  have hclosed (b : Bool) : (P b).closedStrip ⊆ (P b).map '' (DiskV ×ˢ J) := by
    apply image_mono
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hdisP := hdis.mono (hclosed false) (hclosed true)
  have hdisQ : Disjoint (P false).closedStrip Q.closedStrip := by
    simpa only [OriginalDiskProduct.closedStrip, hmap] using hdisP
  have hopen₀ : IsOpen ((Subtype.val : ↥(R \ U.map '' openTube r) → X) ⁻¹'
      (P false).openStrip) := hopen false (1/2) (by norm_num) (by norm_num)
  have hopen₁ : IsOpen ((Subtype.val : (P false).cutCarrier → X) ⁻¹' Q.openStrip) := by
    have hinc : Continuous (Set.inclusion
        (show (P false).cutCarrier ⊆ R \ U.map '' openTube r from sdiff_subset)) :=
      continuous_inclusion _
    rw [OriginalDiskProduct.openStrip, hmap]
    exact (hopen true (1/2) (by norm_num) (by norm_num)).preimage hinc
  obtain ⟨b, hb, hbi, hinter, hcover, ha, hai, haimage, hperiod, hAnnSlice⟩ :=
    exists_final_cut_annulus U hR hI.1 hw hr1.le P F ρ hρ hρr hwρ
      hmark harms hlateral Q hmap hdisQ hopen₀ hopen₁
  have hgeo := neighborhood_final_cut_overlap U hR hI.1 hw hr1.le P F ρ
    hρ hρr hwρ hmark harms hlateral Q hmap hdisQ hopen₀ hopen₁
  have haimage' : pairCylinder b '' ((sphere (0 : P2) 1) ×ˢ I) =
      (⋃ i : Bool × Bool, U.map '' panel r (w/2) i) ∪
        ((P false).endDisks ∪ (P true).endDisks) := by
    rw [haimage, pieceParameter_range U P]
    exact hgeo.1
  have hball : ChartwisePLBall e Q.cutCarrier
      (pairCylinder b '' ((sphere (0 : P2) 1) ×ˢ I) ∪ (g₀ '' c₀ ∪ g₁ '' c₁)) := by
    rw [haimage']
    exact ball
  obtain ⟨HB₀, k, hkPL, hkv, hki, hkimage, hann, hbottom, hktop, hkside⟩ :=
    exists_final_ball_product_of_end_disk_images hI.1.compatible hc₀ hc₁ ha hai
      hg₀ hg₁ hi₀ hi₁ ((hAnnSlice 0 (by norm_num)).trans hrim₀)
      (hrim₁.symm.trans (hAnnSlice 1 (by norm_num)).symm)
      (by rw [haimage', inter_comm]; exact hcontact₀)
      (by rw [haimage', inter_comm]; exact hcontact₁) hgdis.symm hball
  obtain ⟨HN, hNvalue, hNzero, _⟩ := exists_tube_and_strips_product U hR hI.1 hw
    hr1.le P F ρ hρ hρr hwρ hmark harms hlateral hdisP
  have hr : 0 < r := (hρ false).trans (hρr false)
  let : CompactSpace (⋃ i, range (pieceBottom U P r i)) :=
    isCompact_iff_compactSpace.mp (isCompact_pieceBottom_union U P hr hr1.le)
  have hwr : w / 2 < r := by
    have h := (div_le_iff₀ (hρ false)).mp (hwρ false)
    linarith [hρr false]
  obtain ⟨HB, hHB, Hfinal, hfinalN, hfinalB⟩ :=
    exists_homeomorph_of_actual_marked_panel_rim U hw hwr P hNvalue hbi hperiod
      hkv hann hinter
  have hbaseN : range (fun x => (HN (x, ⟨0, by norm_num⟩) : X)) =
      (⋃ i, range (pieceBottom U P r i)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change (HN (y, ⟨0, by norm_num⟩) : X) ∈ _
      rw [hNzero]
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, hNzero _⟩
  have hbaseB : range (fun y => (HB (y, ⟨0, by norm_num⟩) : X)) = g₀ '' c₀ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change (HB (y, ⟨0, by norm_num⟩) : X) ∈ _
      rw [hHB]
      exact hbottom.subset ⟨(y, 0), ⟨y.property, rfl⟩, rfl⟩
    · intro hx
      obtain ⟨⟨z, t⟩, ⟨hz, ht⟩, hzx⟩ := hbottom.symm.subset hx
      have ht' : t = 0 := ht
      subst t
      exact ⟨⟨z, hz⟩, (hHB _ _).trans hzx⟩
  have hbase := congrArg₂ (fun A B : Set X => A ∪ B) hbaseN hbaseB
  let H := ((Homeomorph.setCongr hbase.symm).prodCongr (Homeomorph.refl I)).trans
    (Hfinal.trans (Homeomorph.setCongr hcover))
  have hslice (t : I) : range (fun x => (H (x, t) : X)) =
      range (fun x => (HN (x, t) : X)) ∪ range (fun z => (HB (z, t) : X)) := by
    rw [← ProductGluing.attached_slice_range _ _ (fun p => (HN p : X)) (fun p => (HB p : X))
      (fun p => (Hfinal p : X)) hfinalN hfinalB t]
    ext x
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨⟨y, hbase.symm.subset y.property⟩, hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨⟨y, hbase.subset y.property⟩, hy⟩
  have hNslices (t : I) : range (fun x => (HN (x, t) : X)) =
      ⋃ i, range (fun z => pieceParameter U P r i (z, t)) := by
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩
      rcases mem_iUnion.mp hy with ⟨i, z, rfl⟩
      exact mem_iUnion.mpr ⟨i, z, (hNvalue i z t).symm⟩
    · intro hx
      rcases mem_iUnion.mp hx with ⟨i, z, rfl⟩
      exact ⟨⟨pieceBottom U P r i z, mem_iUnion.mpr ⟨i, mem_range_self z⟩⟩,
        hNvalue i z t⟩
  have hBtop : range (fun y => (HB (y, ⟨1, by norm_num⟩) : X)) = g₁ '' c₁ := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      change (HB (z, ⟨1, by norm_num⟩) : X) ∈ _
      rw [hHB]
      exact (hktop _ ⟨z.property, by norm_num⟩).mpr rfl
    · intro hx
      have hxB : x ∈ Q.cutCarrier := hball.boundary_subset (Or.inr (Or.inr hx))
      obtain ⟨⟨z, t⟩, hp, hzx⟩ := hkimage.symm.subset hxB
      have ht : t = 1 := (hktop _ hp).mp (hzx.symm ▸ hx)
      subst t
      exact ⟨⟨z, hp.1⟩, (hHB _ _).trans hzx⟩
  have hHN (x : (⋃ i, range (pieceBottom U P r i))) (t : I) :
      (H (⟨x, Or.inl x.property⟩, t) : X) = HN (x, t) := by
    change (Hfinal (⟨x, _⟩, t) : X) = HN (x, t)
    have hx : (⟨x, hbase.symm.subset (Or.inl x.property)⟩ :
        ↥(range (fun y => (HN (y, ⟨0, by norm_num⟩) : X)) ∪
          range (fun y => (HB (y, ⟨0, by norm_num⟩) : X)))) =
        ⟨(HN (x, ⟨0, by norm_num⟩) : X), Or.inl (mem_range_self x)⟩ :=
      Subtype.ext (hNzero x).symm
    rw [hx, hfinalN]
  let q : Disk → ((⋃ i, range (pieceBottom U P r i)) ∪ g₀ '' c₀ : Set X) :=
    fun z => ⟨(HB (z, ⟨0, by norm_num⟩) : X),
      Or.inr (hbaseB.subset (mem_range_self z))⟩
  have hq (z : Disk) (t : I) : (H (q z, t) : X) = k (z, t) :=
    (hfinalB z t).trans (hHB z t)
  have hkInj : InjOn k (Disk ×ˢ I) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hki.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hpieceFront := pieceMap_mem_original_frontier_iff U hR hI.1 hw hr1.le P F ρ
    hρ hρr hwρ hmark harms hlateral
  have hannFront : ∀ z ∈ sphere (0 : P2) 1, ∀ t ∈ I,
      pairCylinder b (z, t) ∈ frontier R ↔ t = 0 ∨ t = 1 := by
    intro z hz t ht
    have hx := (hAnnSlice t ht).subset (mem_image_of_mem (pairCylinder b)
      (show (z, t) ∈ sphere (0 : P2) 1 ×ˢ {t} from ⟨hz, rfl⟩))
    rcases mem_iUnion.mp hx with ⟨i, ⟨u, v⟩, ⟨hu, hv⟩, heq⟩
    have hv' : v = t := hv
    subst v
    obtain ⟨l, p, hp, hpoint⟩ := panelFamily_exists_piece_base U P hw hwr i hu
    rw [← heq, hpoint t]
    exact hpieceFront l hp ht
  have hkFront {z : P2} (hz : z ∈ Disk) {t : ℝ} (ht : t ∈ I) :
      k (z, t) ∈ frontier R ↔ t = 0 ∨ t = 1 := by
    apply final_ball_original_frontier_iff hQc.isClosed
      (fun _ hx => hcover.subset (Or.inr hx)) hkInj hkimage hann hbottom hktop hkside
      _ (hold₀.trans sdiff_subset) (hold₁.trans sdiff_subset) hannFront hz ht
    rw [haimage']
    exact hQfront
  have hHfront : ∀ x t, (H (x, t) : X) ∈ frontier R ↔ (t : ℝ) = 0 ∨ (t : ℝ) = 1 := by
    intro x t
    rcases x.property with hx | hx
    · rcases mem_iUnion.mp hx with ⟨i, z, hz⟩
      have hxz : x = ⟨pieceBottom U P r i z,
          Or.inl (mem_iUnion.mpr ⟨i, mem_range_self z⟩)⟩ := Subtype.ext hz.symm
      have hv := (hHN ⟨pieceBottom U P r i z, mem_iUnion.mpr ⟨i, mem_range_self z⟩⟩ t).trans
        (hNvalue i z t)
      rw [hxz, hv]
      exact hpieceFront i z.property t.property
    · obtain ⟨z, hz⟩ := hbaseB.symm.subset hx
      have hxq : x = q z := Subtype.ext hz.symm
      rw [hxq, hq]
      exact hkFront z.property t.property
  have hzero : ∀ x, (H (x, ⟨0, by norm_num⟩) : X) = x := by
    intro x
    rcases x.property with hx | hx
    · exact (hHN ⟨x, hx⟩ ⟨0, by norm_num⟩).trans (hNzero _)
    · obtain ⟨z, hz⟩ := hbaseB.symm.subset hx
      have hxq : x = q z := Subtype.ext hz.symm
      rw [hxq, hq]
      exact (hHB z ⟨0, by norm_num⟩).symm
  have htopImage : range (fun x => (H (x, ⟨1, by norm_num⟩) : X)) =
      (⋃ i, range (fun z => pieceParameter U P r i (z, ⟨1, by norm_num⟩))) ∪ g₁ '' c₁ := by
    rw [hslice, hNslices, hBtop]
  have hwhole := ProductGluing.whole_ends_of_frontier_recognition hR hconn H hHfront
  choose K hK hKs using fun i => exists_filledPieceBase_triangulation hr i
  have hfilledPL (i) : PolyhedralPLInCharts e (filledPieceMap U P k i) ((K i).space ×ˢ I) := by
    rw [hKs]
    exact (filledPieceMap_properties U P hr hr1.le hkPL hkInj i).1
  have hfilledInj (i) : InjOn (filledPieceMap U P k i) ((K i).space ×ˢ I) := by
    rw [hKs]
    exact (filledPieceMap_properties U P hr hr1.le hkPL hkInj i).2
  have hfilledCover : (⋃ i, filledPieceMap U P k i '' ((K i).space ×ˢ {0})) =
      (⋃ i, range (pieceBottom U P r i)) ∪ g₀ '' c₀ := by
    simp_rw [hKs]
    rw [filledPieceMap_bottom_image, hbottom]
  have hfilledValue : ∀ i (x : (K i).space) (t : I),
      (H (⟨filledPieceMap U P k i (x, 0), hfilledCover ▸ mem_iUnion.mpr
        ⟨i, ⟨(x, 0), ⟨x.property, rfl⟩, rfl⟩⟩⟩, t) : X) =
        filledPieceMap U P k i (x, t) := by
    intro i x t
    cases i with
    | none =>
      let z : Disk := ⟨x, (hKs none).subset x.property⟩
      have hxq : (⟨k (x, 0), hfilledCover ▸ mem_iUnion.mpr
          ⟨none, ⟨(x, 0), ⟨x.property, rfl⟩, rfl⟩⟩⟩ :
          ↥((⋃ i, range (pieceBottom U P r i)) ∪ g₀ '' c₀)) = q z :=
        Subtype.ext (hHB z ⟨0, by norm_num⟩).symm
      change (H (⟨k (x, 0), _⟩, t) : X) = k (x, t)
      rw [hxq]
      exact hq z t
    | some i =>
      let z : pieceBase r i := ⟨x, (hKs (some i)).subset x.property⟩
      exact (hHN ⟨pieceBottom U P r i z, mem_iUnion.mpr ⟨i, mem_range_self z⟩⟩ t).trans
        (hNvalue i z t)
  have hgraph := ProductGluing.exists_finitePL_graph_product hI.1 hR K hK
    (filledPieceMap U P k) hfilledPL hfilledInj hfilledCover H hfilledValue
  refine ⟨H, hzero, htopImage, ?_,
    ⟨k, q, hkPL, hkInj, fun z => hHB z ⟨0, by norm_num⟩, hbaseB, hq⟩,
    hHfront, ?_, hgraph⟩
  · intro i z t
    exact (hHN ⟨pieceBottom U P r i z, mem_iUnion.mpr ⟨i, mem_range_self z⟩⟩ t).trans
      (hNvalue i z t)
  · intro x
    refine ⟨?_, (hwhole.2.2.2 x).trans htopImage⟩
    simpa only [hzero, Subtype.range_coe] using hwhole.2.2.1 x

end PoincareConjecture.M76.Dehn.Annuli.ProductConstruction
