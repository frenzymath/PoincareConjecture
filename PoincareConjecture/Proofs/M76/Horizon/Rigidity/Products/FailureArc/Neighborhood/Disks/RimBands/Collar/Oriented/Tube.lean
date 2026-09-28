import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Oriented.Rectangles
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.NormalizedCorners
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusPeriod

set_option autoImplicit false

open Poincare.Topology.Orientation.ProjectivePlane
open Set Metric Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior TubeExterior.CornerBands

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)

theorem exists_original_unsigned_marked_disk_products_of_tube_of_localOrientation
    {X ι : Type} [TopologicalSpace X] [T2Space X]
    (O : LocalOrientation X)
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W Ann Ann C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    (hf₀ : PolyhedralPLInCharts e f₀ Ann) (hf₁ : PolyhedralPLInCharts e f₁ Ann)
    (hi₀ : InjOn f₀ Ann) (hi₁ : InjOn f₁ Ann)
    (hR₀ : MapsTo f₀ Ann R) (hR₁ : MapsTo f₁ Ann R)
    (hp₀ : ∀ z ∈ Ann, f₀ z ∈ frontier R ↔ z ∈ frontier Ann)
    (hp₁ : ∀ z ∈ Ann, f₁ z ∈ frontier R ↔ z ∈ frontier Ann)
    (houter₀ : (C ∩ {z : P2 | depth 8 z = -1}).Nonempty)
    (hinner₀ : (C ∩ {z : P2 | depth 8 z = 1}).Nonempty)
    (houter₁ : (D ∩ {z : P2 | depth 8 z = -1}).Nonempty)
    (hinner₁ : (D ∩ {z : P2 | depth 8 z = 1}).Nonempty)
    (hmeet : Ann ∩ f₀ ⁻¹' (f₁ '' Ann) = C) :
    ∃ (k : Bool → P2 → X) (w : ℝ) (ρ : Bool → ℝ)
      (P : ∀ side, OriginalDiskProduct e (R \ U.map '' openTube (1 / 2))
        (k side ∘ CubeCoordinates.toRectangle))
      (F : Bool → V2 × ℝ → X),
      (∀ side, PolyhedralPLInCharts e (k side) Rect) ∧
      (∀ side, IsEmbedding (fun z : Rect => k side z)) ∧
      (∀ side, MapsTo (k side) Rect (R \ U.map '' openTube (1 / 2))) ∧
      (∀ side, ∀ z ∈ Rect,
        k side z ∈ frontier (R \ U.map '' openTube (1 / 2)) ↔ z ∈ frontier Rect) ∧
      (∀ side, k side '' Rect =
        (if side then f₁ '' Ann else f₀ '' Ann) ∩ (R \ U.map '' openTube (1 / 2))) ∧
      (∀ side, ∀ z ∈ Rect, k side z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1) ∧
      (∀ side, ∀ t ∈ I, k side (0, t) =
        originalBandMap U (1 / 2) (true, if side then false else true) (0, t)) ∧
      (∀ side, ∀ t ∈ I, k side (1, t) =
        originalBandMap U (1 / 2) (false, if side then true else false) (0, t)) ∧
      Disjoint (k false '' Rect) (k true '' Rect) ∧
      0 < w ∧ (∀ side, 0 < ρ side) ∧ (∀ side, ρ side < 1 / 2) ∧
      (∀ side, w / ρ side ≤ 1) ∧
      (∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
        (P side).map (z, s) = F side (z, (w / ρ side) * s)) ∧
      (∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
        F side (rimArmPoint b t, s) =
          prescribedArmBand U (1 / 2) (ρ side) 0 1 side b (s, t)) ∧
      (∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
        F side (z, s) ∈ U.map '' lateral (1 / 2) ↔
          ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t) ∧
      Disjoint ((P false).map '' (Disk ×ˢ J)) ((P true).map '' (Disk ×ˢ J)) ∧
      ∀ side, ∀ v : ℝ, 0 < v → v ≤ 1 →
        IsOpen ((Subtype.val : ↥(R \ U.map '' openTube (1 / 2)) → X) ⁻¹'
          ((P side).map '' (Disk ×ˢ Ioo (-v) v))) := by
  classical
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  have hr1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨V, hVmap, _, _, _, hVopen⟩ :=
    TubeExterior.OriginalIntervalTube.exists_rescaling_with_open_image U hr hr1.le
  obtain ⟨M₀, k₀, hk₀, hki₀, hkQ₀, hkp₀, hcarrier₀, _, himage₀, hfront₀, hleft₀, hright₀⟩ :=
    TubeExterior.OriginalIntervalTube.exists_first_normalized_corner_matched_rectangle
      U V hVmap hR he hf₀ hi₀ hR₀ hp₀ houter₀ hinner₀
  obtain ⟨M₁, k₁, hk₁, hki₁, hkQ₁, hkp₁, hcarrier₁, _, himage₁, hfront₁, hleft₁, hright₁⟩ :=
    TubeExterior.OriginalIntervalTube.exists_second_normalized_corner_matched_rectangle
      U V hVmap hR he hf₁ hi₁ hR₁ hp₁ houter₁ hinner₁
  rw [hVopen] at hkQ₀ hkQ₁ hkp₀ hkp₁ himage₀ himage₁
  let k : Bool → P2 → X := fun side => if side then k₁ else k₀
  have hk : ∀ side, PolyhedralPLInCharts e (k side) Rect := by
    intro side
    cases side <;> assumption
  have hki : ∀ side, IsEmbedding (fun z : Rect => k side z) := by
    intro side
    cases side <;> assumption
  have hkQ : ∀ side, MapsTo (k side) Rect (R \ U.map '' openTube (1 / 2)) := by
    intro side
    cases side <;> assumption
  have hkp : ∀ side, ∀ z ∈ Rect,
      k side z ∈ frontier (R \ U.map '' openTube (1 / 2)) ↔ z ∈ frontier Rect := by
    intro side
    cases side <;> assumption
  have himage : ∀ side, k side '' Rect =
      (if side then f₁ '' Ann else f₀ '' Ann) ∩ (R \ U.map '' openTube (1 / 2)) := by
    intro side
    cases side <;> assumption
  have hfront : ∀ side, ∀ z ∈ Rect, k side z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1 := by
    intro side
    cases side <;> assumption
  have hleft : ∀ side, ∀ t ∈ I, k side (0, t) =
      originalBandMap U (1 / 2) (true, if side then false else true) (0, t) := by
    intro side
    cases side <;> assumption
  have hright : ∀ side, ∀ t ∈ I, k side (1, t) =
      originalBandMap U (1 / 2) (false, if side then true else false) (0, t) := by
    intro side
    cases side <;> assumption
  have hkdis : Disjoint (k false '' Rect) (k true '' Rect) := by
    change Disjoint (k₀ '' Rect) (k₁ '' Rect)
    rw [hcarrier₀, hcarrier₁]
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    exact disjoint_left.mp M₀.avoids_center hx
      (hmeet.subset ⟨M₀.subset_annulus hx, ⟨y, M₁.subset_annulus hy, hxy⟩⟩)
  obtain ⟨A, hA, hAs⟩ := _root_.Dehn.exists_finite_square_annulus_complex
    (L := 8) (d := 1) (by norm_num) (by norm_num)
  let : CompactSpace A.space := isCompact_iff_compactSpace.mp (A.isCompact_space_of_finite hA)
  have hsource : ∀ side : Bool, A.space = if side then Ann else Ann := by
    intro side
    simpa using hAs
  have hf : ∀ side : Bool, PolyhedralPLInCharts e (if side then f₁ else f₀) A.space := by
    intro side
    rw [hAs]
    cases side <;> assumption
  have hinj (side : Bool) : InjOn (if side then f₁ else f₀) A.space := by
    rw [hAs]
    cases side <;> assumption
  have hemb (side : Bool) : IsEmbedding (fun z : A.space => (if side then f₁ else f₀) z) :=
    ((hf side).continuousOn.domRestrict.isClosedEmbedding
      (fun x y hxy => Subtype.ext (hinj side x.property y.property hxy))).isEmbedding
  have hproper : ∀ side : Bool, ∀ z ∈ A.space,
      (if side then f₁ else f₀) z ∈ frontier R ↔ z ∈ frontier A.space := by
    intro side
    rw [hAs]
    cases side <;> assumption
  obtain ⟨w, ρ, P, F, hw, hρ, hρr, hwρ, hmark, harms, hlateral, hdis, hopen⟩ :=
    exists_original_unsigned_marked_disk_products_of_rectangles_of_localOrientation O hR he U
      (fun _ => A) (fun _ => hA) hsource hf hemb hproper hr hr1 k
      hk hki hkQ hkp himage hleft hright hkdis
  exact ⟨k, w, ρ, P, F, hk, hki, hkQ, hkp, himage, hfront, hleft, hright, hkdis,
    hw, hρ, hρr, hwρ, hmark, harms, hlateral, hdis, hopen⟩

end PoincareConjecture.M76.Dehn.Annuli.RimBands
