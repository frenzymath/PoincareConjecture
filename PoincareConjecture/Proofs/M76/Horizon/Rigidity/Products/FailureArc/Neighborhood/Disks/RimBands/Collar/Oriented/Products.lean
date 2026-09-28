import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Oriented.ArmOrientation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.NormalizedPair
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.Geometry

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

theorem exists_original_unsigned_marked_disk_products_of_localOrientation
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
    {r w : ℝ} (hr : 0 < r) (hr1 : r < 1) (hw : 0 < w)
    {j : Bool → V2 → X}
    (P : ∀ side, OriginalDiskProduct e (R \ U.map '' openTube r) (j side))
    (himage : ∀ side, j side '' Disk =
      (if side then f₁ '' T else f₀ '' S) ∩ (R \ U.map '' openTube r))
    (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ) (o : Bool → Bool → Bool)
    (hρ : ∀ side, 0 < ρ side) (hwρ : ∀ side, w / ρ side ≤ 1)
    (hmark : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
      (P side).map (z, s) = F side (z, (w / ρ side) * s))
    (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F side (rimArmPoint b t, s) =
        prescribedArmBand U r (ρ side) 0 1 side b (sign (o side b) * s, t))
    (hlateral : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
      F side (z, s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    (hdis : Disjoint ((P false).map '' (Disk ×ˢ J)) ((P true).map '' (Disk ×ˢ J)))
    (hopen : ∀ side, ∀ v : ℝ, 0 < v → v ≤ 1 →
      IsOpen ((Subtype.val : ↥(R \ U.map '' openTube r) → X) ⁻¹'
        ((P side).map '' (Disk ×ˢ Ioo (-v) v)))) :
    ∃ (P' : ∀ side, OriginalDiskProduct e (R \ U.map '' openTube r) (j side))
      (F' : Bool → V2 × ℝ → X),
      (∀ side, (P' side).map = (P side).map ∘ bandTimeScale (sign (o side false))) ∧
      (∀ side, F' side = F side ∘ bandTimeScale (sign (o side false))) ∧
      (∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
        (P' side).map (z, s) = F' side (z, (w / ρ side) * s)) ∧
      (∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
        F' side (rimArmPoint b t, s) = prescribedArmBand U r (ρ side) 0 1 side b (s, t)) ∧
      (∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
        F' side (z, s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t) ∧
      Disjoint ((P' false).map '' (Disk ×ˢ J)) ((P' true).map '' (Disk ×ˢ J)) ∧
      (∀ side, ∀ v : ℝ, 0 < v → v ≤ 1 →
        IsOpen ((Subtype.val : ↥(R \ U.map '' openTube r) → X) ⁻¹'
          ((P' side).map '' (Disk ×ˢ Ioo (-v) v)))) ∧
      (∀ side a, (P' side).map '' (Disk ×ˢ Icc (-a) a) =
        (P side).map '' (Disk ×ˢ Icc (-a) a)) ∧
      ∀ side a, (P' side).map '' (Disk ×ˢ Ioo (-a) a) =
        (P side).map '' (Disk ×ˢ Ioo (-a) a) := by
  let : LocallyCompactSpace X := he.locallyCompactSpace
  have hQ : IsClosed (R \ U.map '' openTube r) :=
    (TubeExterior.OriginalIntervalTube.isCompact_exterior U hR he hr hr1.le).isClosed
  have hcoherent (side : Bool) : o side false = o side true :=
    orientation_eq_of_original_band_arms_of_localOrientation O he U side (K side) (hK side) (hKs side)
      (hf side) (hi side) (hproper side) hr hr1 (hρ side) hw (hwρ side)
      (P side) hQ sdiff_subset (himage side) (F side) (o side) (hmark side) (harms side)
  exact exists_unsigned_marked_disk_products U P F ρ o hmark harms hlateral hdis hopen hcoherent

end PoincareConjecture.M76.Dehn.Annuli.RimBands
