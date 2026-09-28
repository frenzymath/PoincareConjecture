import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.CollarLift
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Coordinates.ArmIncidence
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSmallDiskProduct

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior TubeExterior.CornerBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1
local notation "Rect" => (J ×ˢ J : Set P2)

structure IntervalBandLift {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e Q j) (F : P2 → X) (a : ℝ → V2) where
  width : ℝ
  positive : 0 < width
  small : width ≤ 1 / 2
  coordinates : P2 → E
  finitePL : FinitePiecewiseAffineOn coordinates (parameter width)
  injective : InjOn coordinates (parameter width)
  mapsTo : MapsTo coordinates (parameter width) (Rim ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2))
  center : ∀ t ∈ J, coordinates (0,t) = (a t,0)
  physical : ∀ p ∈ parameter width, P.map (coordinates p) = F p
  zero_iff : ∀ p ∈ parameter width, (coordinates p).2 = 0 ↔ p.1=0

theorem exists_original_disk_collar_with_arm_lifts
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R) {r δ t₀ t₁ : ℝ}
    (hδ : 0 < δ) (hδr : δ < r) (hr1 : r < 1)
    (horder : (t₀=0 ∧ t₁=1) ∨ (t₀=1 ∧ t₁=0)) (j : Bool) {k : P2 → X}
    (hk : PolyhedralPLInCharts e k Rect) (hki : IsEmbedding (fun p : Rect => k p))
    (hkQ : MapsTo k Rect (R \ U.map '' openTube r))
    (hkproper : ∀ p ∈ Rect, k p ∈ frontier (R \ U.map '' openTube r) ↔ p ∈ frontier Rect)
    (himage : k '' Rect = (if j then f₁ '' T else f₀ '' S) ∩ (R \ U.map '' openTube r))
    (hleft : ∀ t ∈ J, k (0,t) = originalBandMap U r (true,if j then false else true)
      (0,(1-t)*t₀+t*t₁))
    (hright : ∀ t ∈ J, k (1,t) = originalBandMap U r (false,if j then true else false)
      (0,(1-t)*t₀+t*t₁)) :
    ∃ P : OriginalDiskProduct e (R \ U.map '' openTube r) (k ∘ CubeCoordinates.toRectangle),
      (∀ v : ℝ, 0 < v → v ≤ 1 →
        IsOpen ((Subtype.val : (R \ U.map '' openTube r : Set X) → X) ⁻¹'
          (P.map '' (Disk ×ˢ Ioo (-v) v))) ∧
        IsOpen ((Subtype.val : frontier (R \ U.map '' openTube r) → X) ⁻¹'
          (P.map '' (Rim ×ˢ Ioo (-v) v)))) ∧
      ∀ b : Bool, Nonempty (IntervalBandLift P
        (prescribedArmBand U r δ t₀ t₁ j b) (rimArm b)) := by
  have hQ := TubeExterior.OriginalIntervalTube.plDomain_exterior U hR he (hδ.trans hδr) hr1
  have hQc := TubeExterior.OriginalIntervalTube.isCompact_exterior U hR he (hδ.trans hδr) hr1.le
  obtain ⟨hj,hji,hjQ,hjp,_⟩ := CubeCoordinates.original_disk_of_rectangle hk hki hkQ hkproper
  obtain ⟨P,_,hopen⟩ := exists_small_original_disk_product hQc hQ hj hji hjQ hjp
    isOpen_univ (subset_univ _)
  refine ⟨P,hopen,?_⟩
  intro b
  obtain ⟨hF,hFi,hFQ,_⟩ := prescribedArmBand_properties U hR he hδ hδr hr1.le horder j b
  have hFinj : InjOn (prescribedArmBand U r δ t₀ t₁ j b) (parameter 1) :=
    fun p hp q hq heq => congrArg Subtype.val (hFi.injective
      (a₁ := ⟨p,hp⟩) (a₂ := ⟨q,hq⟩) heq)
  obtain ⟨ε,inverse,hε,hεsmall,_,_,_,hq,hqi,hqm,hcenter,hphysical,hzero⟩ :=
    exists_interval_band_lift P hQ (hopen (1 / 2) (by norm_num) (by norm_num)).1
      hF hFinj hFQ (rimArm b) (fun _ ht => rimArm_mem ht)
      (fun t ht => prescribedArmBand_center_on_disk U j hleft hright b ht)
      (fun p hp => prescribedArmBand_disk_iff U hR he hδ hδr hr1 horder j b himage hp)
  exact ⟨{
    width := ε
    positive := hε
    small := hεsmall
    coordinates := inverse ∘ prescribedArmBand U r δ t₀ t₁ j b
    finitePL := hq
    injective := hqi
    mapsTo := hqm
    center := hcenter
    physical := hphysical
    zero_iff := hzero }⟩

end PoincareConjecture.M76.Dehn.Annuli.RimBands
