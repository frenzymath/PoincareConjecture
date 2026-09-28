import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.Outward.FullStrip
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.EndComponents



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductPieces
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}
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

include hR he hw hr1 F ρ hρ hρr hwρ hmark harms hlateral

theorem full_diskStrip_slice_subset_component
    (b : Bool) (t : I) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) :
    (fun p : P2 => diskStrip (P b) (p,t)) '' (I ×ˢ J) ⊆
      connectedComponentIn (frontier R) (U.map ((0,0),t)) := by
  let q : P2 := (0,0)
  have hq : q ∈ I ×ˢ J := by norm_num [q]
  have hqhalf : q ∈ stripBase := by norm_num [q, stripBase]
  have hqC := closed_longitudinal_slice_subset_component U hR he hw hr1 P F ρ hρ hρr
    hwρ hmark harms hlateral t ht
      (mem_iUnion.mpr ⟨some b, ⟨⟨q,hqhalf⟩,rfl⟩⟩)
  have hconn : IsPreconnected ((fun p : P2 => diskStrip (P b) (p,t)) '' (I ×ˢ J)) :=
    ((convex_Icc (0 : ℝ) 1).prod (convex_Icc (-1 : ℝ) 1)).isPreconnected.image _
      (continuousOn_full_diskStrip_slice (P b) t.property)
  have hsub := hconn.subset_connectedComponentIn (mem_image_of_mem _ hq) (by
    rintro x ⟨p,hp,rfl⟩
    exact (full_diskStrip_mem_original_frontier_iff U hR he (hρ b) (hρr b) hr1
      hw (hwρ b) (P b) (F b) b (hmark b) (harms b) (hlateral b) hp t.property).mpr ht)
  change diskStrip (P b) (q,t) ∈ connectedComponentIn (frontier R) (U.map ((0,0),t)) at hqC
  rwa [← connectedComponentIn_eq hqC] at hsub

omit harms in
theorem full_diskStrip_outside_neighborhood
    (hdis : Disjoint ((P false).map '' (Disk ×ˢ J)) ((P true).map '' (Disk ×ˢ J)))
    (b : Bool) {p : P2} (hx : p.1 ∈ Ioo (0 : ℝ) 1) (hs : p.2 ∈ J)
    (hout : p.2 ∉ Icc (-(1/2 : ℝ)) (1/2)) {t : ℝ} (ht : t ∈ I) :
    diskStrip (P b) (p,t) ∉
      U.map '' closedTube r ∪ ((P false).closedStrip ∪ (P true).closedStrip) := by
  have hp : p ∈ I ×ˢ J := ⟨⟨hx.1.le,hx.2.le⟩,hs⟩
  have hz : CubeCoordinates.fromRectangle (p.1,t) ∈ Disk :=
    (CubeCoordinates.toRectangle_mem_iff _).mp
      (by rw [CubeCoordinates.toRectangle_fromRectangle]; exact ⟨hp.1,ht⟩)
  have hfull : diskStrip (P b) (p,t) ∈ (P b).map '' (Disk ×ˢ J) :=
    ⟨(CubeCoordinates.fromRectangle (p.1,t),p.2),⟨hz,hs⟩,rfl⟩
  have hown : diskStrip (P b) (p,t) ∉ (P b).closedStrip := by
    rintro ⟨⟨z,s⟩,⟨hz',hs'⟩,heq⟩
    have hsJ : s ∈ J := ⟨by linarith [hs'.1],by linarith [hs'.2]⟩
    have hinj := (P b).injective ⟨hz',hsJ⟩ ⟨hz,hs⟩ heq
    have heqs : s = p.2 := congrArg Prod.snd hinj
    exact hout (heqs ▸ hs')
  have hclosed_full (c : Bool) : (P c).closedStrip ⊆ (P c).map '' (Disk ×ˢ J) := by
    apply image_mono
    rintro ⟨z,s⟩ ⟨hz,hs⟩
    exact ⟨hz,by linarith [hs.1],by linarith [hs.2]⟩
  rintro (hTube | hStrip)
  · obtain ⟨c,hc⟩ := (full_diskStrip_mem_closedTube_iff U hR he
      ((hρ b).trans (hρr b)) hr1 (div_pos hw (hρ b)) (hwρ b) (P b) (F b)
      (hmark b) (hlateral b) hp ht).mp hTube
    cases c <;> simp only [Bool.false_eq_true,if_false,if_true] at hc <;>
      linarith [hx.1,hx.2]
  · cases b
    · rcases hStrip with h | h
      · exact hown h
      · exact disjoint_left.mp hdis hfull (hclosed_full true h)
    · rcases hStrip with h | h
      · exact disjoint_left.mp hdis (hclosed_full false h) hfull
      · exact hown h

theorem cap_rim_mem_closure_component_complement
    (hdis : Disjoint ((P false).map '' (Disk ×ˢ J)) ((P true).map '' (Disk ×ˢ J)))
    (b : Bool) {x : ℝ} (hx : x ∈ I) {s : ℝ}
    (hs : s = -(1/2 : ℝ) ∨ s = 1/2)
    (t : I) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) :
    diskStrip (P b) ((x,s),t) ∈ closure
      (connectedComponentIn (frontier R) (U.map ((0,0),t)) \
        (U.map '' closedTube r ∪ ((P false).closedStrip ∪ (P true).closedStrip))) := by
  have hcap (l u : ℝ) (hlu : l < u) (hJ : Ioo l u ⊆ J)
      (hout : Disjoint (Ioo l u) (Icc (-(1/2 : ℝ)) (1/2)))
      (hsJ : s ∈ J) (hslu : s ∈ Icc l u) :
      diskStrip (P b) ((x,s),t) ∈ closure
        (connectedComponentIn (frontier R) (U.map ((0,0),t)) \
          (U.map '' closedTube r ∪ ((P false).closedStrip ∪ (P true).closedStrip))) := by
    let A : Set P2 := Ioo (0 : ℝ) 1 ×ˢ Ioo l u
    have hA : A ⊆ I ×ˢ J := fun p hp => ⟨⟨hp.1.1.le,hp.1.2.le⟩,hJ hp.2⟩
    have hcl : (x,s) ∈ closure A := by
      rw [closure_prod_eq,closure_Ioo zero_ne_one,closure_Ioo hlu.ne]
      exact ⟨hx,hslu⟩
    apply ((continuousOn_full_diskStrip_slice (P b) t.property (x,s)
      ⟨hx,hsJ⟩).mono hA).mem_closure hcl
    intro p hp
    refine ⟨full_diskStrip_slice_subset_component U hR he hw hr1 P F ρ hρ hρr hwρ
      hmark harms hlateral b t ht (mem_image_of_mem _ (hA hp)),?_⟩
    exact full_diskStrip_outside_neighborhood U hR he hw hr1 P F ρ hρ hρr hwρ
      hmark hlateral hdis b hp.1 (hJ hp.2) (fun h => disjoint_left.mp hout hp.2 h)
      t.property
  rcases hs with rfl | rfl
  · apply hcap (-1) (-(1/2)) (by norm_num)
    · intro z hz; constructor <;> linarith [hz.1,hz.2]
    · apply disjoint_left.mpr
      intro z hz hz'; linarith [hz.2,hz'.1]
    · norm_num
    · norm_num
  · apply hcap (1/2) 1 (by norm_num)
    · intro z hz; constructor <;> linarith [hz.1,hz.2]
    · apply disjoint_left.mpr
      intro z hz hz'; linarith [hz.1,hz'.2]
    · norm_num
    · norm_num

end PoincareConjecture.M76.Dehn.Annuli.ProductPieces
