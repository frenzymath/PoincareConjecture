import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.TubeAndStrips
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.Assembly.PanelFamily



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductPieces
open TubeExterior TubeExterior.CornerBands BoundaryAssembly PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W Q : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X} {j : Bool → V2 → X}

theorem unitPanelMap_exists_base
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r δ : ℝ} (hδ : 0 < δ) (hδr : δ < r)
    (i : Bool × Bool) (reverse : Bool) {x : ℝ} (hx : x ∈ I) :
    ∃ q ∈ transverseSquare r, ∀ t : ℝ, unitPanelMap U r δ i reverse (x,t) = U.map (q,t) := by
  let q := (panelAffine r i (panelCoordinates r δ reverse (x,0))).1
  have hparam := (panelCoordinates_bijOn hδr reverse).1
    (show (x,(0 : ℝ)) ∈ I ×ˢ I from ⟨hx,by norm_num⟩)
  have hpanel := (panelAffine_image r δ i).subset (mem_image_of_mem (panelAffine r i) hparam)
  have hq : q ∈ transverseSquare r :=
    (lateral_subset r (panel_subset_lateral hδ hδr i hpanel)).1
  refine ⟨q,hq,?_⟩
  intro t
  apply congrArg U.map
  rcases i with ⟨axis,s⟩
  cases axis <;> rfl

theorem panelFamily_exists_piece_base
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (P : ∀ b, OriginalDiskProduct e Q (j b))
    {r w : ℝ} (hw : 0 < w) (hwr : w/2 < r)
    (i : Fin 8) {x : ℝ} (hx : x ∈ I) :
    ∃ k : Option Bool, ∃ q ∈ pieceBase r k, ∀ t : ℝ,
      panelFamily U (P false) (P true) r w i (x,t) = pieceMap U P k (q,t) := by
  have hpanel (a : Bool × Bool) (b : Bool) :=
    unitPanelMap_exists_base U (by linarith : 0 < w/2) hwr a b hx
  have hx' : 1-x ∈ I := ⟨by linarith [hx.2],by linarith [hx.1]⟩
  fin_cases i <;> simp only [panelFamily,Matrix.cons_val_zero',Matrix.cons_val_succ',
    Function.comp_apply,rectangleReflection_apply]
  · obtain ⟨q,hq,hv⟩ := hpanel (false,false) true
    exact ⟨none,q,hq,hv⟩
  · exact ⟨some true,(1-x,-1/2),⟨hx',by norm_num⟩,fun _ => rfl⟩
  · obtain ⟨q,hq,hv⟩ := hpanel (true,false) false
    exact ⟨none,q,hq,hv⟩
  · exact ⟨some false,(1-x,1/2),⟨hx',by norm_num⟩,fun _ => rfl⟩
  · obtain ⟨q,hq,hv⟩ := hpanel (false,true) false
    exact ⟨none,q,hq,hv⟩
  · exact ⟨some true,(x,1/2),⟨hx,by norm_num⟩,fun _ => rfl⟩
  · obtain ⟨q,hq,hv⟩ := hpanel (true,true) true
    exact ⟨none,q,hq,hv⟩
  · exact ⟨some false,(x,-1/2),⟨hx,by norm_num⟩,fun _ => rfl⟩

theorem panelFamily_product_value
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (P : ∀ b, OriginalDiskProduct e Q (j b))
    {r w : ℝ} (hw : 0 < w) (hwr : w/2 < r)
    (H : (⋃ k, range (pieceBottom U P r k)) × I ≃ₜ
      (⋃ k, range (pieceParameter U P r k)))
    (hvalue : ∀ k x t, (H (⟨pieceBottom U P r k x,
      mem_iUnion.mpr ⟨k,mem_range_self x⟩⟩,t) : X) = pieceParameter U P r k (x,t))
    (i : Fin 8) {x : ℝ} (hx : x ∈ I) :
    ∃ hbase : panelFamily U (P false) (P true) r w i (x,0) ∈
        ⋃ k, range (pieceBottom U P r k),
      ∀ t : I, (H (⟨panelFamily U (P false) (P true) r w i (x,0),hbase⟩,t) : X) =
        panelFamily U (P false) (P true) r w i (x,t) := by
  obtain ⟨k,q,hq,hqval⟩ := panelFamily_exists_piece_base U P hw hwr i hx
  have hbase : panelFamily U (P false) (P true) r w i (x,0) ∈
      ⋃ k, range (pieceBottom U P r k) := by
    rw [hqval 0]
    exact mem_iUnion.mpr ⟨k,⟨⟨q,hq⟩,rfl⟩⟩
  refine ⟨hbase,?_⟩
  intro t
  have harg : (⟨panelFamily U (P false) (P true) r w i (x,0),hbase⟩ :
      (⋃ k, range (pieceBottom U P r k))) =
      ⟨pieceBottom U P r k ⟨q,hq⟩,mem_iUnion.mpr ⟨k,mem_range_self _⟩⟩ :=
    Subtype.ext (hqval 0)
  rw [harg,hvalue,hqval t]
  rfl

end PoincareConjecture.M76.Dehn.Annuli.ProductPieces
