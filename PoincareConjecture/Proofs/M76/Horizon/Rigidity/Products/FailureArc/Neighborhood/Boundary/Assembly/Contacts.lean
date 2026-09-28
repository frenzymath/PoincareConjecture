import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.Matching.CapSides
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.Matching.Pair
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CornerBands.OriginalGeometry



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.BoundaryAssembly
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)

theorem arcMap_mem_edgeFootprint_iff {r δ s : ℝ}
    (hδ : 0 < δ) (hδr : δ < r) (hs : s ∈ Icc (-δ) δ)
    (i j : Bool × Bool) :
    arcMap r i s ∈ edgeFootprint r δ j ↔
      incident i j ∧ s = if j.1 then δ else -δ := by
  have hi := arcMap_mem_footprint (r := r) hδ.le i hs
  have hc := footprint_inter_edgeFootprint hδ hδr i j
  by_cases hij : incident i j
  · rw [if_pos hij] at hc
    constructor
    · intro hx
      have heq : arcMap r i s = seamPoint r δ i j.1 := hc.subset ⟨hi,hx⟩
      exact ⟨hij,arcMap_injective r i heq⟩
    · rintro ⟨_,rfl⟩
      exact (hc.symm.subset (show seamPoint r δ i j.1 ∈ {seamPoint r δ i j.1} from rfl)).2
  · rw [if_neg hij] at hc
    exact ⟨fun hx => False.elim (notMem_empty _ (hc.subset ⟨hi,hx⟩)),
      fun hx => False.elim (hij hx.1)⟩

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

omit [T2Space X] in
theorem originalBandMap_mem_panel_iff
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r δ s t : ℝ} (hδ : 0 < δ) (hδr : δ < r) (hr1 : r ≤ 1)
    (hs : s ∈ Icc (-δ) δ) (ht : t ∈ I) (i j : Bool × Bool) :
    originalBandMap U r i (s,t) ∈ U.map '' panel r δ j ↔
      incident i j ∧ s = if j.1 then δ else -δ := by
  have hband : bandMap r i (s,t) ∈ band r δ i :=
    (bandMap_image hδ.le i).subset ⟨(s,t),⟨hs,ht⟩,rfl⟩
  have hbtube : bandMap r i (s,t) ∈ tube := closedTube_subset hr1
    (lateral_subset r (band_subset_lateral hδ.le hδr.le i hband))
  have hiff : originalBandMap U r i (s,t) ∈ U.map '' panel r δ j ↔
      bandMap r i (s,t) ∈ panel r δ j := by
    constructor
    · rintro ⟨z,hz,hzval⟩
      have hztube : z ∈ tube := closedTube_subset hr1
        (lateral_subset r (panel_subset_lateral hδ hδr j hz))
      have heq := congrArg Subtype.val (U.embedding.injective
        (a₁ := ⟨z,hztube⟩) (a₂ := ⟨_,hbtube⟩) hzval)
      change z = bandMap r i (s,t) at heq
      exact heq ▸ hz
    · intro hz
      exact ⟨_,hz,rfl⟩
  rw [hiff]
  change (arcMap r i s ∈ edgeFootprint r δ j ∧ t ∈ I) ↔ _
  rw [and_iff_left ht,arcMap_mem_edgeFootprint_iff hδ hδr hs]

noncomputable def capLevel (negative : Bool) : ℝ := if negative then -(1 / 2) else 1 / 2

def matchingArm (side : Bool) (i : Bool × Bool) : Bool :=
  if side && i.1 then !i.2 else i.2

def capAdjacent (side negative : Bool) (i : Bool × Bool) : Prop :=
  i.1 = (matchingArm side i == negative)

instance (side negative : Bool) (i : Bool × Bool) : Decidable (capAdjacent side negative i) :=
  inferInstanceAs (Decidable (i.1 = (matchingArm side i == negative)))

theorem incident_arm_iff (side b : Bool) (i : Bool × Bool) :
    incident (b,if side then !b else b) i ↔ b = matchingArm side i := by
  rcases i with ⟨axis,s⟩
  cases side <;> cases b <;> cases axis <;> cases s <;>
    simp [incident,matchingArm]

theorem capLevel_mem (negative : Bool) : capLevel negative ∈ J := by
  cases negative <;> norm_num [capLevel]

theorem cap_arm_parameter {ρ a : ℝ} (negative b : Bool) :
    (ρ*a)*(sign b*capLevel negative) =
      if b == negative then ρ*a/2 else -(ρ*a/2) := by
  cases b <;> cases negative <;> simp [sign,capLevel] <;> ring

theorem cap_arm_incidence_iff {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a)
    (side negative b : Bool) (i : Bool × Bool) :
    (incident (b,if side then !b else b) i ∧
      (ρ*a)*(sign b*capLevel negative) = if i.1 then ρ*a/2 else -(ρ*a/2)) ↔
      b = matchingArm side i ∧ capAdjacent side negative i := by
  rw [incident_arm_iff,cap_arm_parameter]
  constructor
  · rintro ⟨rfl,h⟩
    refine ⟨rfl,?_⟩
    unfold capAdjacent
    have hp : 0 < ρ*a := mul_pos hρ ha
    cases hi : i.1 <;> cases hb : (matchingArm side i == negative) <;>
      simp only [hi,hb,Bool.false_eq_true,if_false,if_true] at h ⊢ <;> linarith
  · rintro ⟨rfl,h⟩
    exact ⟨rfl,by rw [show i.1 = (matchingArm side i == negative) from h]⟩

theorem capRectangle_mem_panel_iff
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r ρ a t₀ t₁ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr1 : r ≤ 1)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (horder : (t₀=0 ∧ t₁=1) ∨ (t₀=1 ∧ t₁=0))
    {j : V2 → X} (P : OriginalDiskProduct e (R \ U.map '' openTube r) j)
    (F : V2 × ℝ → X) (side negative : Bool)
    (hmark : ∀ z ∈ Rim, ∀ s ∈ J, P.map (z,s) = F (z,a*s))
    (harms : ∀ b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F (rimArmPoint b t,s) = prescribedArmBand U r ρ t₀ t₁ side b (s,t))
    (hlateral : ∀ z ∈ Rim, ∀ s ∈ J,
      F (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    (i : Bool × Bool) {p : P2} (hp : p ∈ Rect) :
    capRectangle P (capLevel negative) p ∈ U.map '' panel r (ρ*a/2) i ↔
      p.1 = (if matchingArm side i then 0 else 1) ∧ capAdjacent side negative i := by
  have hδ : 0 < ρ*a/2 := div_pos (mul_pos hρ ha) (by norm_num)
  have hδr : ρ*a/2 < r := by nlinarith
  have hs := capLevel_mem negative
  have has : a*capLevel negative ∈ J := by
    constructor <;> nlinarith [hs.1,hs.2]
  have htime (t : ℝ) (ht : t ∈ I) : (1-t)*t₀+t*t₁ ∈ I := by
    rcases horder with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp only [mul_zero,mul_one,zero_add,add_zero]
    · exact ht
    · exact ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hedge := capRectangle_prescribed_arm_edges P F U r ρ t₀ t₁ side ha ha1 hmark harms
  have harm (b : Bool) (t : ℝ) (ht : t ∈ I) :
      capRectangle P (capLevel negative) (if b then 0 else 1,t) ∈
        U.map '' panel r (ρ*a/2) i ↔ b = matchingArm side i ∧ capAdjacent side negative i := by
    rw [hedge b t ht _ hs]
    have hq : (ρ*a)*(sign b*capLevel negative) ∈ Icc (-(ρ*a/2)) (ρ*a/2) := by
      rw [cap_arm_parameter]
      split <;> constructor <;> linarith
    rw [originalBandMap_mem_panel_iff U hδ hδr hr1 hq (htime t ht)]
    exact cap_arm_incidence_iff hρ ha side negative b i
  constructor
  · intro hcap
    have hlat : capRectangle P (capLevel negative) p ∈ U.map '' lateral r :=
      image_mono (panel_subset_lateral hδ hδr i) hcap
    have hfront : capRectangle P (capLevel negative) p ∈ frontier (R \ U.map '' openTube r) := by
      rw [TubeExterior.OriginalIntervalTube.frontier_exterior U hR he (hρ.trans hρr) hr1]
      exact Or.inr hlat
    have hpr : p ∈ frontier Rect := ((capRectangle_properties P hs).2.2.2.2 p hp).mp hfront
    have hz : CubeCoordinates.fromRectangle p ∈ Rim :=
      (CubeCoordinates.toRectangle_rim_iff _).mp
        ((CubeCoordinates.toRectangle_fromRectangle p).symm ▸ hpr)
    have hF : F (CubeCoordinates.fromRectangle p,a*capLevel negative) ∈ U.map '' lateral r := by
      rw [← hmark _ hz _ hs]
      exact hlat
    obtain ⟨b,t,ht,hpt⟩ := (hlateral _ hz _ has).mp hF
    have hpeq : p = (if b then 0 else 1,t) := by
      rw [← fromRectangle_arm] at hpt
      simpa only [CubeCoordinates.toRectangle_fromRectangle] using
        congrArg CubeCoordinates.toRectangle hpt
    have h := (harm b t ht).mp (hpeq ▸ hcap)
    exact ⟨by rw [hpeq,h.1],h.2⟩
  · rintro ⟨hx,hadj⟩
    have hpeq : p = (if matchingArm side i then 0 else 1,p.2) := Prod.ext hx rfl
    rw [hpeq]
    exact (harm _ _ hp.2).mpr ⟨rfl,hadj⟩

theorem capRectangle_inter_panel
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r ρ a t₀ t₁ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr1 : r ≤ 1)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (horder : (t₀=0 ∧ t₁=1) ∨ (t₀=1 ∧ t₁=0))
    {j : V2 → X} (P : OriginalDiskProduct e (R \ U.map '' openTube r) j)
    (F : V2 × ℝ → X) (side negative : Bool)
    (hmark : ∀ z ∈ Rim, ∀ s ∈ J, P.map (z,s) = F (z,a*s))
    (harms : ∀ b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F (rimArmPoint b t,s) = prescribedArmBand U r ρ t₀ t₁ side b (s,t))
    (hlateral : ∀ z ∈ Rim, ∀ s ∈ J,
      F (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    (i : Bool × Bool) :
    (capRectangle P (capLevel negative) '' Rect) ∩ (U.map '' panel r (ρ*a/2) i) =
      if capAdjacent side negative i then
        capRectangle P (capLevel negative) '' ({if matchingArm side i then 0 else 1} ×ˢ I)
      else ∅ := by
  have hiff {p : P2} (hp : p ∈ Rect) := capRectangle_mem_panel_iff U hR he hρ hρr hr1 ha ha1 horder P F
    side negative hmark harms hlateral i hp
  by_cases hadj : capAdjacent side negative i
  · rw [if_pos hadj]
    ext y
    constructor
    · rintro ⟨⟨p,hp,rfl⟩,hy⟩
      exact ⟨p,⟨(hiff hp).mp hy |>.1,hp.2⟩,rfl⟩
    · rintro ⟨p,hp,rfl⟩
      have hpRect : p ∈ Rect := ⟨by rw [hp.1]; split <;> norm_num,hp.2⟩
      exact ⟨⟨p,hpRect,rfl⟩,(hiff hpRect).mpr ⟨hp.1,hadj⟩⟩
  · rw [if_neg hadj]
    apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨⟨p,hp,rfl⟩,hy⟩
    exact hadj ((hiff hp).mp hy).2

theorem capRectangle_subset_closedStrip {Q : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e Q j) (negative : Bool) :
    capRectangle P (capLevel negative) '' Rect ⊆ P.closedStrip := by
  rw [(capRectangle_properties P (capLevel_mem negative)).2.2.2.1]
  apply image_mono (prod_mono subset_rfl ?_)
  intro s hs
  change s = capLevel negative at hs
  subst s
  cases negative <;> norm_num [capLevel]

theorem capRectangles_disjoint_of_disjoint_strips
    {Q₀ Q₁ : Set X} {j₀ j₁ : V2 → X}
    (P₀ : OriginalDiskProduct e Q₀ j₀) (P₁ : OriginalDiskProduct e Q₁ j₁)
    (hdis : Disjoint P₀.closedStrip P₁.closedStrip) (b₀ b₁ : Bool) :
    Disjoint (capRectangle P₀ (capLevel b₀) '' Rect) (capRectangle P₁ (capLevel b₁) '' Rect) :=
  hdis.mono (capRectangle_subset_closedStrip P₀ b₀) (capRectangle_subset_closedStrip P₁ b₁)

theorem four_capRectangles_pairwise_disjoint
    {Q : Set X} {j : Bool → V2 → X} (P : (b : Bool) → OriginalDiskProduct e Q (j b))
    (hdis : Disjoint (P false).closedStrip (P true).closedStrip) :
    Pairwise (fun i k : Bool × Bool =>
      Disjoint (capRectangle (P i.1) (capLevel i.2) '' Rect)
        (capRectangle (P k.1) (capLevel k.2) '' Rect)) := by
  rintro ⟨side₀,b₀⟩ ⟨side₁,b₁⟩ hne
  cases side₀ <;> cases side₁
  · cases b₀ <;> cases b₁
    · exact False.elim (hne rfl)
    · exact (capRectangles_disjoint (P false)).symm
    · exact capRectangles_disjoint (P false)
    · exact False.elim (hne rfl)
  · exact capRectangles_disjoint_of_disjoint_strips (P false) (P true) hdis b₀ b₁
  · exact capRectangles_disjoint_of_disjoint_strips (P true) (P false) hdis.symm b₀ b₁
  · cases b₀ <;> cases b₁
    · exact False.elim (hne rfl)
    · exact (capRectangles_disjoint (P true)).symm
    · exact capRectangles_disjoint (P true)
    · exact False.elim (hne rfl)

def selectedCorner (side b : Bool) : Bool × Bool := (b,if side then !b else b)

def lateralRemainder (r ρ : ℝ) (side : Bool) : Set (P2 × ℝ) :=
  lateral r \ ⋃ b : Bool, openBand r ρ (selectedCorner side b)

theorem lateralRemainder_eq {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (side : Bool) :
    lateralRemainder r ρ side =
      (⋃ b : Bool, band r ρ (selectedCorner (!side) b)) ∪ (⋃ i, panel r ρ i) := by
  have hchoices (i : Bool × Bool) :
      i = selectedCorner side i.1 ∨ i = selectedCorner (!side) i.1 := by
    rcases i with ⟨a,b⟩
    cases side <;> cases a <;> cases b <;> simp [selectedCorner]
  have hne (b c : Bool) : selectedCorner (!side) b ≠ selectedCorner side c := by
    cases side <;> cases b <;> cases c <;> simp [selectedCorner]
  have hopen (i : Bool × Bool) : openBand r ρ i ⊆ band r ρ i :=
    prod_mono (openFootprint_subset r ρ i) subset_rfl
  ext z
  constructor
  · rintro ⟨hz,hn⟩
    by_cases h : z ∈ ⋃ i, openBand r ρ i
    · obtain ⟨i,hi⟩ := mem_iUnion.mp h
      rcases hchoices i with hc | hc
      · exact False.elim (hn (mem_iUnion.mpr ⟨i.1,hc ▸ hi⟩))
      · exact Or.inl (mem_iUnion.mpr ⟨i.1,hc ▸ hopen i hi⟩)
    · exact Or.inr ((lateral_sdiff_openBands hρ hρr).subset ⟨hz,h⟩)
  · rintro (hz | hz)
    · obtain ⟨b,hb⟩ := mem_iUnion.mp hz
      refine ⟨band_subset_lateral hρ.le hρr.le _ hb,?_⟩
      intro hx
      obtain ⟨c,hc⟩ := mem_iUnion.mp hx
      exact disjoint_left.mp (bands_pairwise_disjoint hρr (hne b c)) hb (hopen _ hc)
    · have hh := (lateral_sdiff_openBands hρ hρr).symm.subset hz
      refine ⟨hh.1,?_⟩
      intro hx
      obtain ⟨b,hb⟩ := mem_iUnion.mp hx
      exact hh.2 (mem_iUnion.mpr ⟨selectedCorner side b,hb⟩)

theorem isCompact_lateralRemainder {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (side : Bool) :
    IsCompact (lateralRemainder r ρ side) := by
  rw [lateralRemainder_eq hρ hρr]
  apply IsCompact.union
  · apply isCompact_iUnion
    intro b
    rw [← bandMap_image hρ.le]
    exact (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn
      (bandMap_finitePL r hρ _).continuousOn
  · apply isCompact_iUnion
    intro i
    rw [← panelAffine_image r ρ i]
    exact (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn
      (panelAffine_finitePL hρr i).continuousOn

theorem center_mem_selected_openBand {r ρ t : ℝ} (hρ : 0 < ρ) (ht : t ∈ I)
    (side b : Bool) : bandMap r (selectedCorner side b) (0,t) ∈
      openBand r ρ (selectedCorner side b) := by
  apply (bandMap_open_image hρ.le _).subset
  exact ⟨(0,t),⟨⟨by linarith,by linarith⟩,ht⟩,rfl⟩

omit [T2Space X] in
theorem original_lateralRemainder_geometry
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr1 : r ≤ 1) (side : Bool) :
    IsCompact (U.map '' lateralRemainder r ρ side) ∧
      U.map '' lateralRemainder r ρ side =
        (⋃ b : Bool, U.map '' band r ρ (selectedCorner (!side) b)) ∪
          (⋃ i, U.map '' panel r ρ i) ∧
      ∀ b : Bool, Disjoint
        (originalBandMap U r (selectedCorner side b) '' ({0} ×ˢ I))
        (U.map '' lateralRemainder r ρ side) := by
  have hsub : lateralRemainder r ρ side ⊆ tube :=
    (fun _ hx => closedTube_subset hr1 (lateral_subset r hx.1))
  refine ⟨(isCompact_lateralRemainder hρ hρr side).image_of_continuousOn
    (U.pl.continuousOn.mono hsub),?_,?_⟩
  · rw [lateralRemainder_eq hρ hρr,image_union,image_iUnion,image_iUnion]
  · intro b
    apply disjoint_left.mpr
    rintro y ⟨⟨s,t⟩,⟨hs,ht⟩,hsy⟩ ⟨z,hz,hzy⟩
    change s = 0 at hs
    subst s
    have hcenter := center_mem_selected_openBand (r := r) hρ ht side b
    have hcenterBand : bandMap r (selectedCorner side b) (0,t) ∈
        band r ρ (selectedCorner side b) :=
      ⟨openFootprint_subset r ρ _ hcenter.1,hcenter.2⟩
    have hcenterTube : bandMap r (selectedCorner side b) (0,t) ∈ tube :=
      closedTube_subset hr1 (lateral_subset r (band_subset_lateral hρ.le hρr.le _ hcenterBand))
    have hval := congrArg Subtype.val (U.embedding.injective
      (a₁ := ⟨_,hcenterTube⟩) (a₂ := ⟨z,hsub hz⟩) (hsy.trans hzy.symm))
    change bandMap r (selectedCorner side b) (0,t) = z at hval
    exact hz.2 (mem_iUnion.mpr ⟨b,hval ▸ hcenter⟩)

omit [T2Space X] in
theorem original_lateralRemainder_eq_sdiff
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr1 : r ≤ 1) (side : Bool) :
    U.map '' lateralRemainder r ρ side =
      (U.map '' lateral r) \ ⋃ b : Bool, U.map '' openBand r ρ (selectedCorner side b) := by
  have hlat : lateral r ⊆ tube := (lateral_subset r).trans (closedTube_subset hr1)
  have hinj : InjOn U.map tube := fun z hz w hw h => congrArg Subtype.val
    (U.embedding.injective (a₁ := ⟨z,hz⟩) (a₂ := ⟨w,hw⟩) h)
  have ho : (⋃ b : Bool, openBand r ρ (selectedCorner side b)) ⊆ lateral r := by
    apply iUnion_subset
    intro b
    exact (prod_mono (openFootprint_subset r ρ _) subset_rfl).trans
      (band_subset_lateral hρ.le hρr.le _)
  have h := (hinj.mono hlat).image_sdiff (t := ⋃ b : Bool,openBand r ρ (selectedCorner side b))
  simpa only [inter_eq_right.mpr ho,image_iUnion,lateralRemainder] using h

end PoincareConjecture.M76.Dehn.Annuli.BoundaryAssembly
