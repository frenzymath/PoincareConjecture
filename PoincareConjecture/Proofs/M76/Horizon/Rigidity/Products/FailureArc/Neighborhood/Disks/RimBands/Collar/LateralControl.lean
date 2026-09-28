import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Construction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.Assembly.Contacts

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior TubeExterior.CornerBands BoundaryAssembly PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1

theorem lateral_diagonal_is_center {r : ℝ} (hr : 0 ≤ r) (side : Bool)
    {z : P2 × ℝ} (hz : z ∈ lateral r)
    (hdiag : z.1.2 = if side then -z.1.1 else z.1.1) :
    ∃ b : Bool, bandMap r (selectedCorner side b) (0,z.2)=z := by
  have hf := hz.1
  rw [transverseSquare,frontier_rectangle_eq_four_sides (by linarith) (by linarith)] at hf
  have hx : z.1.1= -r ∨ z.1.1=r := by
    rcases hf with (h | h) | (h | h)
    · have he : z.1.2= -r := h.2
      cases side <;> simp only [Bool.false_eq_true,if_false,if_true] at hdiag
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · have he : z.1.2=r := h.2
      cases side <;> simp only [Bool.false_eq_true,if_false,if_true] at hdiag
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    · exact Or.inl h.1
    · exact Or.inr h.1
  rcases hx with hx | hx
  · refine ⟨true,?_⟩
    cases side <;> simp_all [bandMap,selectedCorner,sign,Prod.ext_iff]
  · refine ⟨false,?_⟩
    cases side <;> simp_all [bandMap,selectedCorner,sign,Prod.ext_iff]

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

omit [T2Space X] in
theorem selected_surface_lateral_subset_centers
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (side : Bool) :
    (if side then f₁ '' T else f₀ '' S) ∩ (U.map '' lateral r) ⊆
      ⋃ b : Bool, originalBandMap U r (selectedCorner side b) '' ({0} ×ˢ J) := by
  rintro y ⟨hy,⟨z,hz,rfl⟩⟩
  have hzt := closedTube_subset hr1 (lateral_subset r hz)
  have hd : z.1.2=if side then -z.1.1 else z.1.1 := by
    cases side
    · exact (U.first_trace z hzt).mp hy
    · exact (U.second_trace z hzt).mp hy
  obtain ⟨b,hb⟩ := lateral_diagonal_is_center hr side hz hd
  exact mem_iUnion.mpr ⟨b,(0,z.2),⟨rfl,hz.2⟩,congrArg U.map hb⟩

omit [T2Space X] in
theorem selected_surface_disjoint_lateralRemainder
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr1 : r ≤ 1) (side : Bool) :
    Disjoint (if side then f₁ '' T else f₀ '' S)
      (U.map '' lateralRemainder r ρ side) := by
  apply disjoint_left.mpr
  intro y hy hrem
  have hlat : y ∈ U.map '' lateral r := image_mono sdiff_subset hrem
  obtain ⟨b,hb⟩ := mem_iUnion.mp
    (selected_surface_lateral_subset_centers U (hρ.trans hρr).le hr1 side ⟨hy,hlat⟩)
  exact disjoint_left.mp ((original_lateralRemainder_geometry U hρ hρr hr1 side).2.2 b) hb hrem

theorem exists_band_width_avoiding_lateralRemainder
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr1 : r ≤ 1) (side : Bool)
    {F : E → X} (hF : ContinuousOn F (Rim ×ˢ I))
    (hcenter : ∀ z ∈ Rim, F (z,0) ∈ (if side then f₁ '' T else f₀ '' S)) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/2 ∧
      MapsTo F (Rim ×ˢ Icc (-a) a) (U.map '' lateralRemainder r ρ side)ᶜ := by
  let f : Rim × I → X := fun p => F (p.1,p.2)
  have hf : Continuous f := hF.comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)) (fun p => ⟨p.1.property,p.2.property⟩)
  have hopen := (original_lateralRemainder_geometry U hρ hρr hr1 side).1.isClosed.isOpen_compl
  have hbase (z : Rim) : f (z,⟨0,by norm_num⟩) ∈
      (U.map '' lateralRemainder r ρ side)ᶜ :=
    disjoint_left.mp (selected_surface_disjoint_lateralRemainder U hρ hρr hr1 side)
      (hcenter z z.property)
  let : CompactSpace Rim := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V2) 1)
  obtain ⟨a,ha,hasmall,hthin⟩ := hf.exists_closed_strip_subset hopen hbase
  refine ⟨a,ha,hasmall,?_⟩
  intro p hp
  have hs : p.2 ∈ I := ⟨by linarith [hp.2.1],by linarith [hp.2.2]⟩
  exact hthin ⟨p.1,hp.1⟩ ⟨p.2,hs⟩ (abs_le.mpr hp.2)

end PoincareConjecture.M76.Dehn.Annuli.RimBands
