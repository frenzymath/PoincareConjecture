import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.TubeAndStrips

set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductPieces
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

theorem diskStrip_mem_original_frontier_iff
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r ρ w : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr1 : r ≤ 1)
    (hw : 0 < w) (hwρ : w / ρ ≤ 1)
    {j : V2 → X} (P : OriginalDiskProduct e (R \ U.map '' openTube r) j)
    (F : V2 × ℝ → X) (side : Bool)
    (hmark : ∀ z ∈ Rim, ∀ s ∈ J, P.map (z,s) = F (z,(w/ρ)*s))
    (harms : ∀ b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F (rimArmPoint b t,s) = prescribedArmBand U r ρ 0 1 side b (s,t))
    (hlateral : ∀ z ∈ Rim, ∀ s ∈ J,
      F (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    {p : P2} (hp : p ∈ stripBase) {t : ℝ} (ht : t ∈ I) :
    diskStrip P (p,t) ∈ frontier R ↔ t = 0 ∨ t = 1 := by
  have hr := hρ.trans hρr
  have ha : 0 < w / ρ := div_pos hw hρ
  have hs : p.2 ∈ J := ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
  have has : (w/ρ)*p.2 ∈ J := by constructor <;> nlinarith [hs.1, hs.2]
  have harm (b : Bool) :
      diskStrip P ((if b then 0 else 1,p.2),t) ∈ frontier R ↔ t = 0 ∨ t = 1 := by
    rw [diskStrip_arm, hmark _ (rimArmPoint_mem_rim b ht) _ hs, harms b t ht _ has]
    exact (prescribedArmBand_properties U hR he hρ hρr hr1
      (Or.inl ⟨rfl, rfl⟩) side b).2.2.2.2.2 _ ⟨has, ht⟩
  have harm' (b : Bool) (hb : p.1 = if b then 0 else 1) :
      diskStrip P (p,t) ∈ frontier R ↔ t = 0 ∨ t = 1 := by
    rw [show p = (if b then 0 else 1,p.2) from Prod.ext hb rfl]
    exact harm b
  have hout := (diskStrip_properties P).2.2.1 (show (p,t) ∈ stripBase ×ˢ I from ⟨hp, ht⟩)
  constructor
  · intro hf
    have hfQ : diskStrip P (p,t) ∈ frontier (R \ U.map '' openTube r) := by
      rw [TubeExterior.OriginalIntervalTube.frontier_exterior U hR he hr hr1]
      exact Or.inl ⟨hf, hout.2⟩
    have hrect : (p.1,t) ∈ frontier (I ×ˢ I : Set P2) :=
      ((capRectangle_properties P hs).2.2.2.2 (p.1,t) ⟨hp.1, ht⟩).mp hfQ
    rw [frontier_prod_eq, isClosed_Icc.closure_eq, frontier_Icc zero_le_one] at hrect
    rcases hrect with ⟨_, hends⟩ | ⟨hends, _⟩
    · simpa only [mem_insert_iff, mem_singleton_iff] using hends
    · rcases hends with hx | hx
      · exact (harm' true hx).mp hf
      · exact (harm' false hx).mp hf
  · intro htend
    have hfQ := diskStrip_end_in_frontier P hp htend
    rw [TubeExterior.OriginalIntervalTube.frontier_exterior U hR he hr hr1] at hfQ
    rcases hfQ with hold | hlat
    · exact hold.1
    · obtain ⟨b, hb⟩ := (diskStrip_mem_closedTube_iff U hR he hr hr1 ha hwρ
        P F hmark hlateral hp ht).mp (image_mono (lateral_subset r) hlat)
      exact (harm' b hb).mpr htend

theorem pieceMap_mem_original_frontier_iff
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r w : ℝ} (hw : 0 < w) (hr1 : r ≤ 1)
    {j : Bool → V2 → X}
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
    (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ)
    (hρ : ∀ b, 0 < ρ b) (hρr : ∀ b, ρ b < r) (hwρ : ∀ b, w/ρ b ≤ 1)
    (hmark : ∀ b, ∀ z ∈ Rim, ∀ s ∈ J, (P b).map (z,s) = F b (z,(w/ρ b)*s))
    (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F side (rimArmPoint b t,s) = prescribedArmBand U r (ρ side) 0 1 side b (s,t))
    (hlateral : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
      F side (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    (i : Option Bool) {p : P2} (hp : p ∈ pieceBase r i) {t : ℝ} (ht : t ∈ I) :
    pieceMap U P i (p,t) ∈ frontier R ↔ t = 0 ∨ t = 1 := by
  cases i with
  | none => exact U.frontier_iff _ (closedTube_subset hr1 ⟨hp, ht⟩)
  | some b =>
    exact diskStrip_mem_original_frontier_iff U hR he (hρ b) (hρr b)
      hr1 hw (hwρ b) (P b) (F b) b (hmark b) (harms b) (hlateral b) hp ht

end PoincareConjecture.M76.Dehn.Annuli.ProductPieces
