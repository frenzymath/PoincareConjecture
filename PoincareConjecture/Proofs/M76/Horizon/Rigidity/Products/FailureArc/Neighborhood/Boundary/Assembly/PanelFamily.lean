import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.Assembly.Coordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.Matching.CapSides

set_option autoImplicit false
noncomputable section
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.BoundaryAssembly
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R Q W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X} {j₀ j₁ : V2 → X}

def panelFamily (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (P₀ : OriginalDiskProduct e Q j₀) (P₁ : OriginalDiskProduct e Q j₁)
    (r w : ℝ) : Fin 8 → P2 → X :=
  ![unitPanelMap U r (w/2) (false,false) true,
    capRectangle P₁ (-1/2) ∘ rectangleReflection,
    unitPanelMap U r (w/2) (true,false) false,
    capRectangle P₀ (1/2) ∘ rectangleReflection,
    unitPanelMap U r (w/2) (false,true) false,
    capRectangle P₁ (1/2),
    unitPanelMap U r (w/2) (true,true) true,
    capRectangle P₀ (-1/2)]

theorem panelFamily_seams
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (P₀ : OriginalDiskProduct e Q j₀) (P₁ : OriginalDiskProduct e Q j₁)
    {r w : ℝ} (hw : 0 < w)
    (h₀ : ∀ b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      capRectangle P₀ s (if b then 0 else 1,t) =
        originalBandMap U r (b,b) (w*(sign b*s),t))
    (h₁ : ∀ b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      capRectangle P₁ s (if b then 0 else 1,t) =
        originalBandMap U r (b,!b) (w*(sign b*s),t)) :
    (∀ i j : Fin 8, i.val+1=j.val → ∀ t ∈ I,
      panelFamily U P₀ P₁ r w i (1,t) = panelFamily U P₀ P₁ r w j (0,t)) ∧
    ∀ t ∈ I, panelFamily U P₀ P₁ r w 7 (1,t) =
      panelFamily U P₀ P₁ r w 0 (0,t) := by
  have hn : max (0 : ℝ) (-(w/2)) = 0 := max_eq_left (by linarith)
  have hp : max (0 : ℝ) (w/2) = w/2 := max_eq_right (by linarith)
  have hns : max (0 : ℝ) (w*(-1/2)) = 0 := max_eq_left (by linarith)
  have hps : max (0 : ℝ) (w*(1/2)) = w*(1/2) := max_eq_right (by linarith)
  have hminus : (-1/2 : ℝ) ∈ J := by norm_num
  have hplus : (1/2 : ℝ) ∈ J := by norm_num
  have edges (t : ℝ) (ht : t ∈ I) :=
    And.intro (And.intro (h₀ false t ht _ hminus) (h₀ true t ht _ hminus))
      (And.intro (And.intro (h₀ false t ht _ hplus) (h₀ true t ht _ hplus))
        (And.intro (And.intro (h₁ false t ht _ hminus) (h₁ true t ht _ hminus))
          (And.intro (h₁ false t ht _ hplus) (h₁ true t ht _ hplus))))
  constructor
  · intro i j hij t ht
    have hs := edges t ht
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals
      simp only [panelFamily,Matrix.cons_val_zero',Matrix.cons_val_succ',
        Function.comp_apply,rectangleReflection_apply,sub_zero,sub_self]
      simp only [Bool.false_eq_true,if_false,if_true,Bool.not_false,Bool.not_true] at hs
      rcases hs with ⟨⟨h00,h01⟩,⟨⟨h02,h03⟩,⟨⟨h10,h11⟩,h12,h13⟩⟩⟩
      first | rw [h00] | rw [h01] | rw [h02] | rw [h03] |
        rw [h10] | rw [h11] | rw [h12] | rw [h13]
      simp only [unitPanelMap,Function.comp_apply,panelCoordinates_apply,
        originalPanelMap,originalBandMap,bandMap,arcMap,panelAffine,sign,
        Bool.false_eq_true,if_false,if_true]
      congr 1
      apply Prod.ext
      · apply Prod.ext <;> dsimp
        all_goals norm_num [mul_div_assoc,mul_neg,hn,hp,hns,hps]
        all_goals ring
        all_goals first | exact hw.le | rw [max_eq_left (by linarith)]
        all_goals ring
      · rfl
  · intro t ht
    have h00 := (edges t ht).1.1
    simp only [Bool.false_eq_true,if_false] at h00
    rw [show panelFamily U P₀ P₁ r w 7 (1,t) = capRectangle P₀ (-1/2) (1,t) from rfl,
      h00]
    simp only [panelFamily,Matrix.cons_val_zero,unitPanelMap,Function.comp_apply,
      panelCoordinates_apply,originalPanelMap,originalBandMap,bandMap,arcMap,
      panelAffine,sign,Bool.false_eq_true,if_false,if_true]
    congr 1
    apply Prod.ext
    · apply Prod.ext <;> dsimp
      all_goals norm_num [mul_div_assoc,mul_neg,hn,hp,hns,hps]
      all_goals ring
      all_goals first | exact hw.le | rw [max_eq_left (by linarith)]
      all_goals ring
    · rfl

theorem panelFamily_seams_of_marked_products
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {j : Bool → V2 → X} (P : ∀ b, OriginalDiskProduct e Q (j b))
    (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ)
    {r w : ℝ} (hw : 0 < w) (hρ : ∀ b, 0 < ρ b) (hwρ : ∀ b, w/ρ b ≤ 1)
    (hmark : ∀ b, ∀ z ∈ sphere (0 : V2) 1, ∀ s ∈ J,
      (P b).map (z,s) = F b (z,(w/ρ b)*s))
    (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F side (rimArmPoint b t,s) = prescribedArmBand U r (ρ side) 0 1 side b (s,t)) :
    (∀ i k : Fin 8, i.val+1=k.val → ∀ t ∈ I,
      panelFamily U (P false) (P true) r w i (1,t) =
        panelFamily U (P false) (P true) r w k (0,t)) ∧
    ∀ t ∈ I, panelFamily U (P false) (P true) r w 7 (1,t) =
      panelFamily U (P false) (P true) r w 0 (0,t) := by
  apply panelFamily_seams U (P false) (P true) hw
  · simpa only [Bool.false_eq_true,if_false] using
      capRectangle_common_width_arm_edges (P false) (F false) U r false
        (hρ false) hw (hwρ false) (hmark false) (harms false)
  · simpa only [if_true] using
      capRectangle_common_width_arm_edges (P true) (F true) U r true
        (hρ true) hw (hwρ true) (hmark true) (harms true)

end PoincareConjecture.M76.Dehn.Annuli.BoundaryAssembly
