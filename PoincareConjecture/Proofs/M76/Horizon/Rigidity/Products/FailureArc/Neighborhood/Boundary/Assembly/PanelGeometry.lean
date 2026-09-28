import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.Assembly.PanelFamily

set_option autoImplicit false
noncomputable section
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.BoundaryAssembly
open TubeExterior TubeExterior.CornerBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R Q W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X} {j₀ j₁ : V2 → X}

theorem panelFamily_pl_injective
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (P₀ : OriginalDiskProduct e Q j₀) (P₁ : OriginalDiskProduct e Q j₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r w : ℝ} (hw : 0 < w) (hwr : w/2 < r) (hr1 : r ≤ 1) :
    ∀ i, PolyhedralPLInCharts e (panelFamily U P₀ P₁ r w i) Rect ∧
      InjOn (panelFamily U P₀ P₁ r w i) Rect := by
  have hj {f : P2 → X} (hi : IsEmbedding (fun p : Rect => f p)) : InjOn f Rect := by
    intro p hp q hq hpq
    exact congrArg Subtype.val (hi.injective (a₁ := ⟨p,hp⟩) (a₂ := ⟨q,hq⟩) hpq)
  have hpanel (i : Bool × Bool) (b : Bool) :
      PolyhedralPLInCharts e (unitPanelMap U r (w/2) i b) Rect ∧
        InjOn (unitPanelMap U r (w/2) i b) Rect := by
    have h := unitPanelMap_properties U hR he (by linarith : 0 < w/2) hwr hr1 i b
    exact ⟨h.1,hj h.2.1⟩
  have hcap {j : V2 → X} (P : OriginalDiskProduct e Q j) (s : ℝ)
      (hs : s ∈ Icc (-1 : ℝ) 1) :
      PolyhedralPLInCharts e (capRectangle P s) Rect ∧ InjOn (capRectangle P s) Rect := by
    have h := capRectangle_properties P hs
    exact ⟨h.1,hj h.2.1⟩
  intro i
  fin_cases i <;> simp only [panelFamily,Matrix.cons_val_zero',Matrix.cons_val_succ']
  · exact hpanel _ _
  · have h := hcap P₁ (-1/2) (by norm_num)
    exact ⟨(reflected_rectangle_properties h.1 h.2).1,
      (reflected_rectangle_properties h.1 h.2).2.1⟩
  · exact hpanel _ _
  · have h := hcap P₀ (1/2) (by norm_num)
    exact ⟨(reflected_rectangle_properties h.1 h.2).1,
      (reflected_rectangle_properties h.1 h.2).2.1⟩
  · exact hpanel _ _
  · exact hcap P₁ (1/2) (by norm_num)
  · exact hpanel _ _
  · exact hcap P₀ (-1/2) (by norm_num)

theorem panelFamily_image
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (P₀ : OriginalDiskProduct e Q j₀) (P₁ : OriginalDiskProduct e Q j₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r w : ℝ} (hw : 0 < w) (hwr : w/2 < r) (hr1 : r ≤ 1) :
    (⋃ i, panelFamily U P₀ P₁ r w i '' Rect) =
      (⋃ i : Bool × Bool, U.map '' panel r (w/2) i) ∪ (P₀.endDisks ∪ P₁.endDisks) := by
  have himage (i : Bool × Bool) (b : Bool) :=
    (unitPanelMap_properties U hR he (by linarith : 0 < w/2) hwr hr1 i b).2.2.1
  rw [← capRectangles_cover_endDisks P₀,← capRectangles_cover_endDisks P₁]
  ext x
  simp only [mem_iUnion,Prod.exists,Fin.exists_fin_succ,Bool.exists_bool,
    panelFamily,Matrix.cons_val_zero,Matrix.cons_val_succ,
    image_comp,rectangleReflection_bijOn.image_eq,himage,mem_union]
  simp only [not_false_eq_true,IsEmpty.exists_iff,false_or,or_false,neg_div]
  tauto

end PoincareConjecture.M76.Dehn.Annuli.BoundaryAssembly
