import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.Assembly.Contacts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.Assembly.PanelGeometry



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.BoundaryAssembly
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)

theorem rectangleReflection_edge_image (s : ℝ) :
    rectangleReflection '' ({s} ×ˢ I) = {1-s} ×ˢ I := by
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨by change 1-p.1 = 1-s; rw [hp.1],hp.2⟩
  · rintro ⟨hs,ht⟩
    exact ⟨(s,z.2),⟨rfl,ht⟩,Prod.ext hs.symm rfl⟩

theorem rectangle_edge_images_eq {X : Type*} (f g : P2 → X) {s t : ℝ}
    (h : ∀ u ∈ I, f (s,u) = g (t,u)) :
    f '' ({s} ×ˢ I) = g '' ({t} ×ˢ I) := by
  ext y
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨(t,p.2),⟨rfl,hp.2⟩,(h p.2 hp.2).symm.trans (congrArg f (Prod.ext hp.1.symm rfl))⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨(s,p.2),⟨rfl,hp.2⟩,(h p.2 hp.2).trans (congrArg g (Prod.ext hp.1.symm rfl))⟩

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

set_option maxHeartbeats 1600000 in
theorem panelFamily_incidence
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r w : ℝ} (hw : 0 < w) (hr1 : r ≤ 1)
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
    (hdis : Disjoint (P false).closedStrip (P true).closedStrip) :
    (∀ i k : Fin 8, i.val+1=k.val →
      ((panelFamily U (P false) (P true) r w i) '' Rect) ∩
        ((panelFamily U (P false) (P true) r w k) '' Rect) =
        (panelFamily U (P false) (P true) r w i) '' ({1} ×ˢ I)) ∧
    (((panelFamily U (P false) (P true) r w 0) '' Rect) ∩
      ((panelFamily U (P false) (P true) r w 7) '' Rect) =
      (panelFamily U (P false) (P true) r w 0) '' ({0} ×ˢ I)) ∧
    ∀ i k : Fin 8, i.val+1<k.val → ¬(i=0 ∧ k=7) →
      Disjoint ((panelFamily U (P false) (P true) r w i) '' Rect)
        ((panelFamily U (P false) (P true) r w k) '' Rect) := by
  have hwr : w/2 < r := by
    have h := (div_le_iff₀ (hρ false)).mp (hwρ false)
    linarith [hρr false]
  have hpanel (i : Bool × Bool) (b : Bool) :
      unitPanelMap U r (w/2) i b '' Rect = U.map '' panel r (w/2) i :=
    (unitPanelMap_properties U hR he (by linarith : 0 < w/2) hwr hr1 i b).2.2.1
  have hreflect (g : P2 → X) : (g ∘ rectangleReflection) '' Rect = g '' Rect := by
    rw [image_comp,rectangleReflection_bijOn.image_eq]
  have hcap (side negative : Bool) (i : Bool × Bool) :
      (capRectangle (P side) (capLevel negative) '' Rect) ∩ (U.map '' panel r (w/2) i) =
        if capAdjacent side negative i then
          capRectangle (P side) (capLevel negative) '' ({if matchingArm side i then 0 else 1} ×ˢ I)
        else ∅ := by
    have h := capRectangle_inter_panel U hR he (hρ side) (hρr side) hr1
      (div_pos hw (hρ side)) (hwρ side) (Or.inl ⟨rfl,rfl⟩) (P side) (F side)
      side negative (hmark side) (harms side) (hlateral side) i
    simpa only [mul_div_cancel₀ _ (hρ side).ne'] using h
  have havoid (side negative : Bool) (i : Bool × Bool) (hn : ¬capAdjacent side negative i) :
      Disjoint (capRectangle (P side) (capLevel negative) '' Rect) (U.map '' panel r (w/2) i) := by
    rw [disjoint_iff_inter_eq_empty,hcap,if_neg hn]
  have hpp := (original_lateral_decomposition U (by linarith : 0 < w/2) hwr hr1).2.2.2
  have hcc := four_capRectangles_pairwise_disjoint P hdis
  obtain ⟨hseam,hclose⟩ := panelFamily_seams_of_marked_products U P F ρ hw hρ hwρ hmark harms
  have hedge (i k : Fin 8) (hik : i.val+1=k.val) :
      panelFamily U (P false) (P true) r w i '' ({1} ×ˢ I) =
        panelFamily U (P false) (P true) r w k '' ({0} ×ˢ I) :=
    rectangle_edge_images_eq _ _ (hseam i k hik)
  have hend := rectangle_edge_images_eq _ _ hclose
  have h01 := hedge 0 1 (by decide)
  have h23 := hedge 2 3 (by decide)
  have h45 := hedge 4 5 (by decide)
  have h67 := hedge 6 7 (by decide)
  change unitPanelMap U r (w/2) (false,false) true '' ({1} ×ˢ I) =
    (capRectangle (P true) (-1/2) ∘ rectangleReflection) '' ({0} ×ˢ I) at h01
  change unitPanelMap U r (w/2) (true,false) false '' ({1} ×ˢ I) =
    (capRectangle (P false) (1/2) ∘ rectangleReflection) '' ({0} ×ˢ I) at h23
  change unitPanelMap U r (w/2) (false,true) false '' ({1} ×ˢ I) =
    capRectangle (P true) (1/2) '' ({0} ×ˢ I) at h45
  change unitPanelMap U r (w/2) (true,true) true '' ({1} ×ˢ I) =
    capRectangle (P false) (-1/2) '' ({0} ×ˢ I) at h67
  change capRectangle (P false) (-1/2) '' ({1} ×ˢ I) =
    unitPanelMap U r (w/2) (false,false) true '' ({0} ×ˢ I) at hend
  constructor
  · intro i k hik
    fin_cases i <;> fin_cases k <;> norm_num at hik
    all_goals simp only [panelFamily,Matrix.cons_val_zero',Matrix.cons_val_succ']
    · rw [h01,hpanel,hreflect,image_comp,rectangleReflection_edge_image,sub_zero,inter_comm]
      simpa [capLevel,capAdjacent,matchingArm,neg_div] using hcap true true (false,false)
    · rw [hreflect,hpanel,image_comp,rectangleReflection_edge_image,sub_self]
      simpa [capLevel,capAdjacent,matchingArm,neg_div] using hcap true true (true,false)
    · rw [h23,hpanel,hreflect,image_comp,rectangleReflection_edge_image,sub_zero,inter_comm]
      simpa [capLevel,capAdjacent,matchingArm] using hcap false false (true,false)
    · rw [hreflect,hpanel,image_comp,rectangleReflection_edge_image,sub_self]
      simpa [capLevel,capAdjacent,matchingArm] using hcap false false (false,true)
    · rw [h45,hpanel,inter_comm]
      simpa [capLevel,capAdjacent,matchingArm] using hcap true false (false,true)
    · rw [hpanel]
      simpa [capLevel,capAdjacent,matchingArm] using hcap true false (true,true)
    · rw [h67,hpanel,inter_comm]
      simpa [capLevel,capAdjacent,matchingArm,neg_div] using hcap false true (true,true)
  constructor
  · change (unitPanelMap U r (w/2) (false,false) true '' Rect) ∩
      (capRectangle (P false) (-1/2) '' Rect) =
      unitPanelMap U r (w/2) (false,false) true '' ({0} ×ˢ I)
    rw [← hend,hpanel,inter_comm]
    simpa [capLevel,capAdjacent,matchingArm,neg_div] using hcap false true (false,false)
  · intro i k hik hnot
    fin_cases i <;> fin_cases k <;> norm_num at hik
    all_goals try norm_num at hnot
    all_goals try exact False.elim (hnot (by decide))
    all_goals
      simp only [panelFamily,Matrix.cons_val_zero',Matrix.cons_val_succ',hreflect,hpanel,neg_div]
      first
      | apply hpp; decide
      | exact @hcc (true,true) (false,false) (by decide)
      | exact @hcc (true,true) (true,false) (by decide)
      | exact @hcc (true,true) (false,true) (by decide)
      | exact @hcc (false,false) (true,false) (by decide)
      | exact @hcc (false,false) (false,true) (by decide)
      | exact @hcc (true,false) (false,true) (by decide)
      | apply havoid false false; decide
      | apply havoid true true; decide
      | apply Disjoint.symm; apply havoid false false; decide
      | apply Disjoint.symm; apply havoid false true; decide
      | apply Disjoint.symm; apply havoid true false; decide

end PoincareConjecture.M76.Dehn.Annuli.BoundaryAssembly
