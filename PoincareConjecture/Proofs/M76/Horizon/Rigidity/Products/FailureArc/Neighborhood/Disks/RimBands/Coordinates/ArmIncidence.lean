import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.LateralArms
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.CubeCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.Domain



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior TubeExterior.CornerBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)

def rimArm (b : Bool) (t : ℝ) : V2 := ![sign b,2*t-1]

theorem rimArm_mem {b : Bool} {t : ℝ} (ht : t ∈ I) : rimArm b t ∈ Rim := by
  rw [← CubeCoordinates.toRectangle_rim_iff]
  have hq : CubeCoordinates.toRectangle (rimArm b t) = (if b then 0 else 1,t) := by
    cases b <;> simp [rimArm,sign]
  rw [hq,frontier_rectangle_eq_four_sides zero_le_one zero_le_one]
  cases b
  · exact Or.inr (Or.inr ⟨rfl,ht⟩)
  · exact Or.inr (Or.inl ⟨rfl,ht⟩)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

theorem prescribedArmBand_selected_sheet_iff
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R) {r δ t₀ t₁ : ℝ}
    (hδ : 0 < δ) (hδr : δ < r) (hr1 : r ≤ 1)
    (horder : (t₀=0 ∧ t₁=1) ∨ (t₀=1 ∧ t₁=0)) (j b : Bool)
    {p : P2} (hp : p ∈ parameter 1) :
    prescribedArmBand U r δ t₀ t₁ j b p ∈ (if j then f₁ '' T else f₀ '' S) ↔ p.1=0 := by
  have hbij := armCoordinates_bijOn hδ horder b
  obtain ⟨_,_,_,hfirst,hsecond,_,_⟩ :=
    originalBandMap_properties U hR he hδ hδr hr1 (b,if j then !b else b)
  cases j
  · change originalBandMap U r (b,b) (armCoordinates δ t₀ t₁ b p) ∈ f₀ '' S ↔ _
    simp only [Bool.false_eq_true,if_false] at hfirst
    rw [hfirst _ (hbij.1 hp),armCoordinates_apply]
    cases b <;> simp [sign,hδ.ne']
  · change originalBandMap U r (b,!b) (armCoordinates δ t₀ t₁ b p) ∈ f₁ '' T ↔ _
    simp only [if_true] at hsecond
    rw [hsecond _ (hbij.1 hp),armCoordinates_apply]
    cases b <;> simp [sign,hδ.ne']

theorem prescribedArmBand_disk_iff
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R) {r δ t₀ t₁ : ℝ}
    (hδ : 0 < δ) (hδr : δ < r) (hr1 : r < 1)
    (horder : (t₀=0 ∧ t₁=1) ∨ (t₀=1 ∧ t₁=0)) (j b : Bool)
    {k : P2 → X}
    (himage : k '' Rect = (if j then f₁ '' T else f₀ '' S) ∩ (R \ U.map '' openTube r))
    {p : P2} (hp : p ∈ parameter 1) :
    prescribedArmBand U r δ t₀ t₁ j b p ∈ (k ∘ CubeCoordinates.toRectangle) '' Disk ↔
      p.1=0 := by
  have hQ := TubeExterior.OriginalIntervalTube.plDomain_exterior U hR he (hδ.trans hδr) hr1
  have hband := (prescribedArmBand_properties U hR he hδ hδr hr1.le horder j b).2.2.1 hp
  have hmaps := hQ.closed.frontier_subset hband
  rw [Set.image_comp,CubeCoordinates.toRectangle_image,himage]
  exact (and_iff_left hmaps).trans
    (prescribedArmBand_selected_sheet_iff U hR he hδ hδr hr1.le horder j b hp)

omit [T2Space X] in
theorem prescribedArmBand_center_on_disk
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r δ t₀ t₁ : ℝ} (j : Bool) {k : P2 → X}
    (hleft : ∀ t ∈ I, k (0,t) = originalBandMap U r (true,if j then false else true)
      (0,(1-t)*t₀+t*t₁))
    (hright : ∀ t ∈ I, k (1,t) = originalBandMap U r (false,if j then true else false)
      (0,(1-t)*t₀+t*t₁)) (b : Bool) {t : ℝ} (ht : t ∈ I) :
    prescribedArmBand U r δ t₀ t₁ j b (0,t) =
      (k ∘ CubeCoordinates.toRectangle) (rimArm b t) := by
  have hcenter : prescribedArmBand U r δ t₀ t₁ j b (0,t) =
      originalBandMap U r (b,if j then !b else b) (0,(1-t)*t₀+t*t₁) := by
    simp only [prescribedArmBand,Function.comp_apply,armCoordinates_apply,mul_zero]
  rw [hcenter]
  cases b
  · simpa [rimArm,sign] using (hright t ht).symm
  · simpa [rimArm,sign] using (hleft t ht).symm

end PoincareConjecture.M76.Dehn.Annuli.RimBands
