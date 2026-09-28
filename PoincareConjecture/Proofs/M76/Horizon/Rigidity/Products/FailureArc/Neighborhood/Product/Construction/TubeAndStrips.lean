import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Contacts.TubeStrip
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Pieces.Tube
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.EmbeddedPrism

set_option autoImplicit false
noncomputable section
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductPieces
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "Rim" => sphere (0 : V2) 1

def pieceBase (r : ℝ) : Option Bool → Set P2
  | none => transverseSquare r
  | some _ => stripBase

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W Q : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X} {j : Bool → V2 → X}

def pieceMap (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (P : ∀ b, OriginalDiskProduct e Q (j b)) : Option Bool → P2 × ℝ → X
  | none => U.map
  | some b => diskStrip (P b)

def pieceParameter (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (P : ∀ b, OriginalDiskProduct e Q (j b)) (r : ℝ) (i : Option Bool) :
    pieceBase r i × I → X := fun z => pieceMap U P i (z.1,z.2)

def pieceBottom (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (P : ∀ b, OriginalDiskProduct e Q (j b)) (r : ℝ) (i : Option Bool) :
    pieceBase r i → X := fun z => pieceMap U P i (z,0)

theorem exists_tube_and_strips_product
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r w : ℝ} (hw : 0 < w) (hr1 : r ≤ 1)
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
    (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ)
    (hρ : ∀ b, 0 < ρ b) (hρr : ∀ b, ρ b < r) (hwρ : ∀ b, w/ρ b ≤ 1)
    (hmark : ∀ b, ∀ z ∈ Rim, ∀ s ∈ J, (P b).map (z,s) = F b (z,(w/ρ b)*s))
    (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F side (rimArmPoint b t,s) = prescribedArmBand U r (ρ side) 0 1 side b (s,t))
    (hlateral : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
      F side (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    (hdis : Disjoint (P false).closedStrip (P true).closedStrip) :
    ∃ H : (⋃ i, range (pieceBottom U P r i)) × I ≃ₜ
        (⋃ i, range (pieceParameter U P r i)),
      (∀ i x t, (H (⟨pieceBottom U P r i x,mem_iUnion.mpr ⟨i,mem_range_self x⟩⟩,t) : X) =
        pieceParameter U P r i (x,t)) ∧
      (∀ x, (H (x,⟨0,by norm_num⟩) : X) = x) ∧
      ∀ i, PolyhedralPLInCharts e (pieceMap U P i) (pieceBase r i ×ˢ I) := by
  have hr : 0 < r := (hρ false).trans (hρr false)
  have hpl (i : Option Bool) :
      PolyhedralPLInCharts e (pieceMap U P i) (pieceBase r i ×ˢ I) := by
    cases i with
    | none => exact (tubePiece_properties U hr hr1).1
    | some b => exact (diskStrip_properties (P b)).1
  have hi (i : Option Bool) : Function.Injective (pieceParameter U P r i) := by
    have hinj : InjOn (pieceMap U P i) (pieceBase r i ×ˢ I) := by
      cases i with
      | none => exact (TubeExterior.OriginalIntervalTube.restrict_closedTube U hr hr1).2.1
      | some b =>
        intro x hx y hy hxy
        exact congrArg Subtype.val ((diskStrip_properties (P b)).2.1.injective
          (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) hxy)
    intro x y hxy
    have h := hinj ⟨x.1.property,x.2.property⟩ ⟨y.1.property,y.2.property⟩ hxy
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have hc (i : Option Bool) : Continuous (pieceParameter U P r i) :=
    (hpl i).continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)) (fun z => ⟨z.1.property,z.2.property⟩)
  have hcross (side : Bool) (x : pieceBase r none) (y : pieceBase r (some side)) (s t : I) :
      pieceParameter U P r none (x,s) = pieceParameter U P r (some side) (y,t) ↔
        pieceBottom U P r none x = pieceBottom U P r (some side) y ∧ s = t := by
    have h := tube_diskStrip_collision_iff U hR he (hρ side) (hρr side) hr1 hw
      (hwρ side) (P side) (F side) side (hmark side) (harms side) (hlateral side)
      x.property y.property s.property t.property
    simpa only [pieceParameter,pieceMap,pieceBottom,Subtype.ext_iff] using h
  have hrange (b : Bool) : range (pieceParameter U P r (some b)) ⊆ (P b).closedStrip := by
    rintro _ ⟨⟨x,t⟩,rfl⟩
    rw [← (diskStrip_properties (P b)).2.2.2]
    exact ⟨((x : P2),(t : ℝ)),⟨x.property,t.property⟩,rfl⟩
  have hsep : Disjoint (range (pieceParameter U P r (some false)))
      (range (pieceParameter U P r (some true))) := hdis.mono (hrange false) (hrange true)
  have hcollision : ∀ i j (x : pieceBase r i) (y : pieceBase r j) (s t : I),
      pieceParameter U P r i (x,s) = pieceParameter U P r j (y,t) ↔
        pieceBottom U P r i x = pieceBottom U P r j y ∧ s = t := by
    intro i j x y s t
    cases i with
    | none =>
      cases j with
      | none => exact ProductGluing.collision_iff_of_injective (hi none) x y s t
      | some b => exact hcross b x y s t
    | some a =>
      cases j with
      | none => simpa only [eq_comm] using hcross a y x t s
      | some b =>
        cases a <;> cases b
        · exact ProductGluing.collision_iff_of_injective (hi _) x y s t
        · exact ProductGluing.collision_iff_of_disjoint_ranges hsep x y s t
        · exact ProductGluing.collision_iff_of_disjoint_ranges hsep.symm x y s t
        · exact ProductGluing.collision_iff_of_injective (hi _) x y s t
  letI (i : Option Bool) : CompactSpace (pieceBase r i) :=
    isCompact_iff_compactSpace.mp (by cases i <;> exact isCompact_Icc.prod isCompact_Icc)
  obtain ⟨H,hvalue,hzero⟩ := ProductGluing.exists_homeomorph_of_parametrized_pieces
    (fun i => pieceBase r i) (pieceBottom U P r) (pieceParameter U P r) hc
    (fun _ _ => rfl) hcollision
  exact ⟨H,hvalue,hzero,hpl⟩

end PoincareConjecture.M76.Dehn.Annuli.ProductPieces
