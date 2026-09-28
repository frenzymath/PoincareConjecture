import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.TubeAndStrips
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.MarkedBall.Construction
import PoincareConjecture.Proofs.M76.PrimeReduction.BallModelCoordinates

set_option autoImplicit false
noncomputable section
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductConstruction

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Disk" => closedBall (0 : P2) 1

open ProductPieces
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W Q : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X} {j : Bool → V2 → X}

local notation "Rim" => sphere (0 : V2) 1
local notation "J" => Icc (-1 : ℝ) 1

theorem pieceParameter_range
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ}
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b)) :
    (⋃ i, range (pieceParameter U P r i)) =
      U.map '' closedTube r ∪ ((P false).closedStrip ∪ (P true).closedStrip) := by
  ext x
  constructor
  · intro hx
    rcases mem_iUnion.mp hx with ⟨i, hi⟩
    cases i with
    | none =>
        rcases hi with ⟨z, rfl⟩
        exact Or.inl ⟨(z.1, z.2), ⟨z.1.property, z.2.property⟩, rfl⟩
    | some b =>
        rcases hi with ⟨z, rfl⟩
        cases b with
        | false =>
            apply Or.inr
            apply Or.inl
            rw [← (diskStrip_properties (P false)).2.2.2]
            exact ⟨(z.1, z.2), ⟨z.1.property, z.2.property⟩, rfl⟩
        | true =>
            apply Or.inr
            apply Or.inr
            rw [← (diskStrip_properties (P true)).2.2.2]
            exact ⟨(z.1, z.2), ⟨z.1.property, z.2.property⟩, rfl⟩
  · intro hx
    rcases hx with hx | hx
    · rcases hx with ⟨p, hp, rfl⟩
      refine mem_iUnion.mpr ⟨none, ⟨⟨⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩⟩, ?_⟩⟩
      rfl
    · rcases hx with hx | hx
      · rcases hx with ⟨p, hp, rfl⟩
        have hx' : (P false).map p ∈ (P false).closedStrip := ⟨p, hp, rfl⟩
        rw [← (diskStrip_properties (P false)).2.2.2] at hx'
        rcases hx' with ⟨q, hq, hqval⟩
        refine mem_iUnion.mpr ⟨some false,
          ⟨(⟨q.1,hq.1⟩,⟨q.2,hq.2⟩), ?_⟩⟩
        simpa [pieceParameter, pieceMap] using hqval
      · rcases hx with ⟨p, hp, rfl⟩
        have hx' : (P true).map p ∈ (P true).closedStrip := ⟨p, hp, rfl⟩
        rw [← (diskStrip_properties (P true)).2.2.2] at hx'
        rcases hx' with ⟨q, hq, hqval⟩
        refine mem_iUnion.mpr ⟨some true,
          ⟨(⟨q.1,hq.1⟩,⟨q.2,hq.2⟩), ?_⟩⟩
        simpa [pieceParameter, pieceMap] using hqval

theorem exists_subtype_product_final_ball
    {B : Set X}
    (H : (Disk ×ˢ I : Set (P2 × ℝ)) ≃ₜ B) :
    ∃ HB : ((Disk : Set P2) × I) ≃ₜ B,
      ∀ z : (Disk : Set P2), ∀ t : I,
        (HB (z, t) : X) = H ((Homeomorph.Set.prod Disk I).symm (z, t)) := by
  let HB : ((Disk : Set P2) × I) ≃ₜ B := (Homeomorph.Set.prod Disk I).symm.trans H
  refine ⟨HB, ?_⟩
  intro z t
  rfl

theorem exists_neighborhood_product_on_actual_carrier
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r w : ℝ} (hw : 0 < w) (hr1 : r ≤ 1)
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
    (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ)
    (hρ : ∀ b, 0 < ρ b) (hρr : ∀ b, ρ b < r) (hwρ : ∀ b, w/ρ b ≤ 1)
    (hmark : ∀ b, ∀ z ∈ Rim, ∀ s ∈ J,
      (P b).map (z,s) = F b (z,(w/ρ b)*s))
    (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F side (rimArmPoint b t,s) = prescribedArmBand U r (ρ side) 0 1 side b (s,t))
    (hlateral : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
      F side (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    (hdis : Disjoint (P false).closedStrip (P true).closedStrip) :
    ∃ HN : ((⋃ i, range (pieceBottom U P r i)) × I) ≃ₜ
        ((U.map '' closedTube r ∪ ((P false).closedStrip ∪ (P true).closedStrip)) : Set X),
      (∀ i x t, (HN (⟨pieceBottom U P r i x,
        mem_iUnion.mpr ⟨i,mem_range_self x⟩⟩,t) : X) =
        pieceParameter U P r i (x,t)) ∧
      ∀ x, (HN (x,⟨0,by norm_num⟩) : X) = x := by
  obtain ⟨H₀,hvalue,hzero,_⟩ := exists_tube_and_strips_product U hR he hw hr1
    P F ρ hρ hρr hwρ hmark harms hlateral hdis
  have htarget := pieceParameter_range U P
  let targetChange := Homeomorph.setCongr htarget
  let HN := H₀.trans targetChange
  refine ⟨HN, ?_, ?_⟩
  · intro i x t
    change (H₀ (⟨pieceBottom U P r i x,
      mem_iUnion.mpr ⟨i,mem_range_self x⟩⟩,t) : X) = _
    exact hvalue i x t
  · intro x
    change (H₀ (x,⟨0,by norm_num⟩) : X) = x
    exact hzero x

end PoincareConjecture.M76.Dehn.Annuli.ProductConstruction
