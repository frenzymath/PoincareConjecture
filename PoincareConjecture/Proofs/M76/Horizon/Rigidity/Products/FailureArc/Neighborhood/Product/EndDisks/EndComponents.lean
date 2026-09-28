import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Pieces.OriginalFrontier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Contacts.PanelDepth
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.Assembly.PanelGeometry



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductPieces
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution BoundaryAssembly

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

omit [T2Space X] in
theorem piece_slice_eq
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {Q : Set X} {j : Bool → V2 → X}
    (P : ∀ b, OriginalDiskProduct e Q (j b)) (r : ℝ) (t : I) :
    (⋃ i, range (fun z => pieceParameter U P r i (z,t))) =
      U.map '' (transverseSquare r ×ˢ {(t : ℝ)}) ∪
        ⋃ b : Bool, diskStrip (P b) '' (stripBase ×ˢ {(t : ℝ)}) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,z,rfl⟩ := mem_iUnion.mp hx
    cases i with
    | none => exact Or.inl ⟨(z,t),⟨z.property,rfl⟩,rfl⟩
    | some b => exact Or.inr (mem_iUnion.mpr ⟨b,⟨(z,t),⟨z.property,rfl⟩,rfl⟩⟩)
  · rintro (hx | hx)
    · obtain ⟨⟨z,s⟩,⟨hz,hs⟩,rfl⟩ := hx
      have hst : s = t := hs
      subst s
      exact mem_iUnion.mpr ⟨none,⟨⟨z,hz⟩,rfl⟩⟩
    · obtain ⟨b,⟨⟨z,s⟩,⟨hz,hs⟩,rfl⟩⟩ := mem_iUnion.mp hx
      have hst : s = t := hs
      subst s
      exact mem_iUnion.mpr ⟨some b,⟨⟨z,hz⟩,rfl⟩⟩

theorem isPreconnected_closed_longitudinal_slice
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r w : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {j : Bool → V2 → X}
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
    (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ)
    (hmark : ∀ b, ∀ z ∈ Rim, ∀ s ∈ J,
      (P b).map (z,s) = F b (z,(w/ρ b)*s))
    (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F side (rimArmPoint b t,s) = prescribedArmBand U r (ρ side) 0 1 side b (s,t))
    (t : I) : IsPreconnected (⋃ i, range (fun z => pieceParameter U P r i (z,t))) := by
  rw [piece_slice_eq]
  let A := U.map '' (transverseSquare r ×ˢ {(t : ℝ)})
  let B := fun b => diskStrip (P b) '' (stripBase ×ˢ {(t : ℝ)})
  have hA : IsPreconnected A :=
    (((convex_Icc (-r) r).prod (convex_Icc (-r) r)).isPreconnected.prod
      isPreconnected_singleton).image U.map
        (U.pl.continuousOn.mono (fun z hz => closedTube_subset hr1 ⟨hz.1,hz.2 ▸ t.property⟩))
  have hB (b : Bool) : IsPreconnected (B b) :=
    (((convex_Icc (0 : ℝ) 1).prod (convex_Icc (-(1/2 : ℝ)) (1/2))).isPreconnected.prod
      isPreconnected_singleton).image (diskStrip (P b))
        ((diskStrip_properties (P b)).1.continuousOn.mono (fun z hz => ⟨hz.1,hz.2 ▸ t.property⟩))
  have hcontact (b : Bool) : ∃ x ∈ A, x ∈ B b := by
    let z : P2 × ℝ := ((r,if b then -r else r),t)
    refine ⟨U.map z,⟨z,⟨⟨⟨by linarith,le_rfl⟩,?_⟩,rfl⟩,rfl⟩,?_⟩
    · cases b <;> dsimp [z] <;> constructor <;> linarith
    · refine ⟨((1,0),t),⟨⟨by norm_num,by norm_num⟩,rfl⟩,?_⟩
      have harm := diskStrip_arm (P b) false 0 t
      simp only [Bool.false_eq_true,if_false] at harm
      rw [harm,hmark b _ (rimArmPoint_mem_rim false t.property) 0 (by norm_num)]
      simp only [mul_zero]
      rw [harms b false t t.property 0 (by norm_num)]
      cases b <;> simp [prescribedArmBand,armCoordinates_apply,originalBandMap,
        bandMap,arcMap,sign,z]
  obtain ⟨x,hxA,hxB⟩ := hcontact false
  obtain ⟨y,hyA,hyB⟩ := hcontact true
  have h := (hA.union x hxA hxB (hB false)).union y (Or.inl hyA) hyB (hB true)
  have hBool : (⋃ b, B b) = B false ∪ B true := by
    ext x
    simp only [mem_iUnion,Bool.exists_bool,mem_union]
  change IsPreconnected (A ∪ ⋃ b, B b)
  rw [hBool,← union_assoc]
  exact h

variable (U : OriginalIntervalTube e R W S T C D f₀ f₁)
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

include hR he hw hr1 F ρ hρ hρr hwρ hmark harms hlateral

theorem closed_longitudinal_slice_subset_component
    (t : I) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) :
    (⋃ i, range (fun z => pieceParameter U P r i (z,t))) ⊆
      connectedComponentIn (frontier R) (U.map ((0,0),t)) := by
  have hr := (hρ false).trans (hρr false)
  apply (isPreconnected_closed_longitudinal_slice U hr hr1 P F ρ hmark harms t).subset_connectedComponentIn
  · exact mem_iUnion.mpr ⟨none,⟨⟨(0,0),⟨⟨by linarith,hr.le⟩,⟨by linarith,hr.le⟩⟩⟩,rfl⟩⟩
  · rintro x hx
    obtain ⟨i,z,rfl⟩ := mem_iUnion.mp hx
    exact (pieceMap_mem_original_frontier_iff U hR he hw hr1 P F ρ hρ hρr hwρ
      hmark harms hlateral i z.property t.property).mpr ht

theorem panelFamily_mem_original_frontier_iff
    (hwr : w/2 < r) (i : Fin 8) {x t : ℝ} (hx : x ∈ I) (ht : t ∈ I) :
    panelFamily U (P false) (P true) r w i (x,t) ∈ frontier R ↔ t = 0 ∨ t = 1 := by
  obtain ⟨k,q,hq,hv⟩ := panelFamily_exists_piece_base U P hw hwr i hx
  rw [hv]
  exact pieceMap_mem_original_frontier_iff U hR he hw hr1 P F ρ hρ hρr hwρ
    hmark harms hlateral k hq ht

theorem panel_rim_subset_component
    (hwr : w/2 < r) (t : ℝ) (ht : t = 0 ∨ t = 1) :
    (⋃ i, panelFamily U (P false) (P true) r w i '' (I ×ˢ {t})) ⊆
      connectedComponentIn (frontier R) (U.map ((0,0),t)) := by
  have htI : t ∈ I := by rcases ht with rfl | rfl <;> norm_num
  apply Subset.trans ?_ (closed_longitudinal_slice_subset_component U hR he hw hr1
    P F ρ hρ hρr hwρ hmark harms hlateral ⟨t,htI⟩ ht)
  intro y hy
  obtain ⟨i,z,hz,rfl⟩ := mem_iUnion.mp hy
  have hzt : z.2 = t := hz.2
  obtain ⟨k,q,hq,hv⟩ := panelFamily_exists_piece_base U P hw hwr i hz.1
  refine mem_iUnion.mpr ⟨k,⟨⟨q,hq⟩,?_⟩⟩
  change pieceMap U P k (q,t) = panelFamily U (P false) (P true) r w i (z.1,z.2)
  rw [hzt]
  exact (hv t).symm

theorem panel_annulus_inter_component_eq_rim
    (hwr : w/2 < r)
    (hdistinct : connectedComponentIn (frontier R) (U.map ((0,0),0)) ≠
      connectedComponentIn (frontier R) (U.map ((0,0),1)))
    (t : ℝ) (ht : t = 0 ∨ t = 1) :
    (⋃ i, panelFamily U (P false) (P true) r w i '' (I ×ˢ I)) ∩
      connectedComponentIn (frontier R) (U.map ((0,0),t)) =
        ⋃ i, panelFamily U (P false) (P true) r w i '' (I ×ˢ {t}) := by
  have hplace := panel_rim_subset_component U hR he hw hr1 P F ρ hρ hρr hwρ
    hmark harms hlateral hwr
  apply Subset.antisymm
  · rintro y ⟨hy,hyt⟩
    obtain ⟨i,z,hz,rfl⟩ := mem_iUnion.mp hy
    have hfront := connectedComponentIn_subset (frontier R) (U.map ((0,0),t)) hyt
    have hzEnd := (panelFamily_mem_original_frontier_iff U hR he hw hr1 P F ρ hρ hρr hwρ
      hmark harms hlateral hwr i hz.1 hz.2).mp hfront
    have hzs := hplace z.2 hzEnd (mem_iUnion.mpr ⟨i,⟨z,⟨hz.1,rfl⟩,rfl⟩⟩)
    have heq := (connectedComponentIn_eq hzs).trans (connectedComponentIn_eq hyt).symm
    have hzt : z.2 = t := by
      rcases hzEnd with hs | hs <;> rcases ht with ht | ht
      · exact hs.trans ht.symm
      · exact False.elim (hdistinct (by simpa only [hs,ht] using heq))
      · exact False.elim (hdistinct (by simpa only [hs,ht] using heq.symm))
      · exact hs.trans ht.symm
    exact mem_iUnion.mpr ⟨i,⟨z,⟨hz.1,hzt⟩,rfl⟩⟩
  · intro y hy
    refine ⟨?_,hplace t ht hy⟩
    obtain ⟨i,z,hz,rfl⟩ := mem_iUnion.mp hy
    refine mem_iUnion.mpr ⟨i,⟨z,⟨hz.1,?_⟩,rfl⟩⟩
    have hzt : z.2 = t := hz.2
    rw [hzt]
    rcases ht with rfl | rfl <;> norm_num

theorem final_panel_annulus_inter_component_eq_rim
    (hwr : w/2 < r)
    (hdistinct : connectedComponentIn (frontier R) (U.map ((0,0),0)) ≠
      connectedComponentIn (frontier R) (U.map ((0,0),1)))
    (t : ℝ) (ht : t = 0 ∨ t = 1) :
    ((⋃ i : Bool × Bool, U.map '' panel r (w/2) i) ∪
      ((P false).endDisks ∪ (P true).endDisks)) ∩
      connectedComponentIn (frontier R) (U.map ((0,0),t)) =
        ⋃ i, panelFamily U (P false) (P true) r w i '' (I ×ˢ {t}) := by
  rw [← panelFamily_image U (P false) (P true) hR he hw hwr hr1]
  exact panel_annulus_inter_component_eq_rim U hR he hw hr1 P F ρ hρ hρr hwρ
    hmark harms hlateral hwr hdistinct t ht

end PoincareConjecture.M76.Dehn.Annuli.ProductPieces
