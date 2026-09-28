import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Oriented.Products
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Partitioned
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.Matching.Pair

set_option autoImplicit false

open Poincare.Topology.Orientation.ProjectivePlane
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior TubeExterior.CornerBands

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)

theorem exists_original_unsigned_marked_disk_products_of_rectangles_of_localOrientation
    {X ι : Type} [TopologicalSpace X] [T2Space X]
    (O : LocalOrientation X)
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (hR : IsCompact R) (he : PLDomain e R)
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (K : Bool → SimplicialComplex ℝ P2) (hK : ∀ side, (K side).faces.Finite)
    (hKs : ∀ side, (K side).space = if side then T else S)
    (hf : ∀ side, PolyhedralPLInCharts e (if side then f₁ else f₀) (K side).space)
    (hi : ∀ side, IsEmbedding (fun z : (K side).space => (if side then f₁ else f₀) z))
    (hproper : ∀ side, ∀ z ∈ (K side).space,
      (if side then f₁ else f₀) z ∈ frontier R ↔ z ∈ frontier (K side).space)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (k : Bool → P2 → X)
    (hk : ∀ side, PolyhedralPLInCharts e (k side) Rect)
    (hki : ∀ side, IsEmbedding (fun z : Rect => k side z))
    (hkQ : ∀ side, MapsTo (k side) Rect (R \ U.map '' openTube r))
    (hkproper : ∀ side, ∀ z ∈ Rect,
      k side z ∈ frontier (R \ U.map '' openTube r) ↔ z ∈ frontier Rect)
    (hkimage : ∀ side, k side '' Rect =
      (if side then f₁ '' T else f₀ '' S) ∩ (R \ U.map '' openTube r))
    (hleft : ∀ side, ∀ t ∈ I,
      k side (0, t) = originalBandMap U r (true, if side then false else true) (0, t))
    (hright : ∀ side, ∀ t ∈ I,
      k side (1, t) = originalBandMap U r (false, if side then true else false) (0, t))
    (hkdis : Disjoint (k false '' Rect) (k true '' Rect)) :
    ∃ (w : ℝ) (ρ : Bool → ℝ)
      (P : ∀ side, OriginalDiskProduct e (R \ U.map '' openTube r)
        (k side ∘ CubeCoordinates.toRectangle))
      (F : Bool → V2 × ℝ → X),
      0 < w ∧ (∀ side, 0 < ρ side) ∧ (∀ side, ρ side < r) ∧
      (∀ side, w / ρ side ≤ 1) ∧
      (∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
        (P side).map (z, s) = F side (z, (w / ρ side) * s)) ∧
      (∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
        F side (rimArmPoint b t, s) = prescribedArmBand U r (ρ side) 0 1 side b (s, t)) ∧
      (∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
        F side (z, s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t) ∧
      Disjoint ((P false).map '' (Disk ×ˢ J)) ((P true).map '' (Disk ×ˢ J)) ∧
      ∀ side, ∀ v : ℝ, 0 < v → v ≤ 1 →
        IsOpen ((Subtype.val : ↥(R \ U.map '' openTube r) → X) ⁻¹'
          ((P side).map '' (Disk ×ˢ Ioo (-v) v))) := by
  classical
  have hδ : 0 < r / 2 := half_pos hr
  have hδr : r / 2 < r := half_lt_self hr
  have hbands (side : Bool) := exists_partitioned_complement_disk_band
    (t₀ := 0) (t₁ := 1) U hR he hδ hδr hr1 (Or.inl ⟨rfl, rfl⟩) side
    (hk side) (hki side) (hkQ side) (hkproper side) (hkimage side)
    (by simpa using hleft side) (by simpa using hright side)
  choose o ρ F hρ hρr hF hFi hFQ hcenter hopenF harms hlateral using hbands
  let j : Bool → V2 → X := fun side => k side ∘ CubeCoordinates.toRectangle
  have hdata (side : Bool) := CubeCoordinates.original_disk_of_rectangle
    (hk side) (hki side) (hkQ side) (hkproper side)
  have hj : ∀ side, PolyhedralPLInCharts e (j side) Disk := fun side => (hdata side).1
  have hji : ∀ side, IsEmbedding (fun z : Disk => j side z) := fun side => (hdata side).2.1
  have hjQ : ∀ side, MapsTo (j side) Disk (R \ U.map '' openTube r) :=
    fun side => (hdata side).2.2.1
  have hjproper : ∀ side, ∀ z : Disk,
      j side z ∈ frontier (R \ U.map '' openTube r) ↔ (z : V2) ∈ Rim :=
    fun side => (hdata side).2.2.2.1
  have hjimage (side : Bool) : j side '' Disk =
      (if side then f₁ '' T else f₀ '' S) ∩ (R \ U.map '' openTube r) :=
    (hdata side).2.2.2.2.1.trans (hkimage side)
  have hjdis : Disjoint (j false '' Disk) (j true '' Disk) := by
    simpa only [j, image_comp, CubeCoordinates.toRectangle_image] using hkdis
  have hQc := TubeExterior.OriginalIntervalTube.isCompact_exterior U hR he hr hr1.le
  have hQ := TubeExterior.OriginalIntervalTube.plDomain_exterior U hR he hr hr1
  obtain ⟨w, hw, P, hwρhalf, hdis, hmark, hopen⟩ :=
    exists_disjoint_original_marked_disk_products hQc hQ j hj hji hjQ hjproper hjdis
      F hF hFi hFQ hcenter hopenF ρ hρ
  have hwρ (side : Bool) : w / ρ side ≤ 1 := (hwρhalf side).trans (by norm_num)
  obtain ⟨P', F', _, _, hmark', harms', hlateral', hdis', hopen', _, _⟩ :=
    exists_original_unsigned_marked_disk_products_of_localOrientation O hR he U K hK hKs hf hi hproper
      hr hr1 hw P hjimage F ρ o hρ hwρ hmark harms hlateral hdis
      (fun side v hv hv1 => (hopen side v hv hv1).1)
  exact ⟨w, ρ, P', F', hw, hρ, hρr, hwρ, hmark', harms', hlateral', hdis', hopen'⟩

end PoincareConjecture.M76.Dehn.Annuli.RimBands
