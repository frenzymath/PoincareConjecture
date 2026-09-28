import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.Outward.Tube
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.Outward.Caps
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.Assembly.LateralCut



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution
open ProductPieces BoundaryAssembly

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



theorem panel_rim_subset_closure_component_complement
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r w : ℝ} (hw : 0 < w) (hr1 : r < 1)
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
    (hdis : Disjoint ((P false).map '' (Disk ×ˢ J)) ((P true).map '' (Disk ×ˢ J)))
    (t : I) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) :
    (Subtype.val : connectedComponentIn (frontier R) (U.map ((0,0),t)) → X) ⁻¹'
      (⋃ i, panelFamily U (P false) (P true) r w i '' (I ×ˢ {(t : ℝ)})) ⊆
    closure (Subtype.val ⁻¹'
      (U.map '' closedTube r ∪ ((P false).closedStrip ∪ (P true).closedStrip))ᶜ) := by
  have hr : 0 < r := (hρ false).trans (hρr false)
  have hwr : w/2 < r := by
    have hwρ' := (div_le_iff₀ (hρ false)).mp (hwρ false)
    linarith [hρr false]
  have hfull (b : Bool) : (P b).closedStrip ⊆ (P b).map '' (Disk ×ˢ J) := by
    apply image_mono
    rintro ⟨z,s⟩ ⟨hz,hs⟩
    exact ⟨hz,by linarith [hs.1],by linarith [hs.2]⟩
  have hclosed : Disjoint (P false).closedStrip (P true).closedStrip :=
    hdis.mono (hfull false) (hfull true)
  obtain ⟨H,hvalue,_,_⟩ := exists_tube_and_strips_product U hR he hw hr1.le
    P F ρ hρ hρr hwρ hmark harms hlateral hclosed
  intro x hx
  obtain ⟨i,z,hz,hzx⟩ := mem_iUnion.mp hx
  have hzt : z.2 = (t : ℝ) := hz.2
  obtain ⟨k,q,hq,hqval⟩ := panelFamily_exists_piece_base U P hw hwr i hz.1
  have hxt : pieceParameter U P r k (⟨q,hq⟩,t) = (x : X) := by
    change pieceMap U P k (q,t) = _
    exact (hqval t).symm.trans ((congrArg (panelFamily U (P false) (P true) r w i)
      (show (z.1,(t : ℝ)) = z from Prod.ext rfl hzt.symm)).trans hzx)
  have hdepth (l : Option Bool) (p : pieceBase r l) (u : I)
      (hpx : pieceParameter U P r l (p,u) = (x : X)) : u = t := by
    have hh := (hvalue l p u).trans
      (hpx.trans (hxt.symm.trans (hvalue k ⟨q,hq⟩ t).symm))
    exact congrArg Prod.snd (H.injective (Subtype.ext hh))
  have hcap (b : Bool) (hxb : (x : X) ∈ (P b).endDisks) :
      x ∈ closure (Subtype.val ⁻¹'
        (U.map '' closedTube r ∪ ((P false).closedStrip ∪ (P true).closedStrip))ᶜ) := by
    rw [← capRectangles_cover_endDisks] at hxb
    obtain ⟨s,hs,p,hp,hpx⟩ : ∃ s : ℝ, (s = -(1/2) ∨ s = 1/2) ∧
        ∃ p ∈ I ×ˢ I, capRectangle (P b) s p = (x : X) := by
      rcases hxb with hxb | hxb
      · obtain ⟨p,hp,hpx⟩ := hxb
        exact ⟨-(1/2),Or.inl rfl,p,hp,hpx⟩
      · obtain ⟨p,hp,hpx⟩ := hxb
        exact ⟨1/2,Or.inr rfl,p,hp,hpx⟩
    have hsb : s ∈ Icc (-(1/2 : ℝ)) (1/2) := by
      rcases hs with rfl | rfl <;> norm_num
    have hu := hdepth (some b) ⟨(p.1,s),hp.1,hsb⟩ ⟨p.2,hp.2⟩ hpx
    have hut : p.2 = (t : ℝ) := congrArg Subtype.val hu
    have hpx' : diskStrip (P b) ((p.1,s),t) = (x : X) := by
      change capRectangle (P b) s (p.1,t) = _
      exact (congrArg (capRectangle (P b) s)
        (show (p.1,(t : ℝ)) = p from Prod.ext rfl hut.symm)).trans hpx
    rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
      Subtype.image_preimage_coe]
    change (x : X) ∈ closure _
    rw [← hpx']
    convert cap_rim_mem_closure_component_complement U hR he hw hr1.le P F ρ hρ hρr
      hwρ hmark harms hlateral hdis b hp.1 hs t ht using 1
    rfl
  have hxin : (x : X) ∈ (⋃ a : Bool × Bool, U.map '' panel r (w/2) a) ∪
      ((P false).endDisks ∪ (P true).endDisks) := by
    rw [← panelFamily_image U (P false) (P true) hR he hw hwr hr1.le]
    exact mem_iUnion.mpr ⟨i,z,⟨hz.1,hzt ▸ t.property⟩,hzx⟩
  rcases hxin with hxpanel | hxcap
  · by_cases hxstrips : (x : X) ∈ (P false).closedStrip ∪ (P true).closedStrip
    · have havoid := ((lateral_sdiff_two_openStrips U hR he hw hr1.le P F ρ hρ hρr
        hwρ hmark harms hlateral).symm.subset hxpanel).2
      rcases hxstrips with hxstrip | hxstrip
      · exact hcap false ((P false).closedStrip_sdiff_openStrip.subset
          ⟨hxstrip,fun h ↦ havoid (Or.inl h)⟩)
      · exact hcap true ((P true).closedStrip_sdiff_openStrip.subset
          ⟨hxstrip,fun h ↦ havoid (Or.inr h)⟩)
    · obtain ⟨a,p,hp,hpx⟩ := mem_iUnion.mp hxpanel
      have hlat := panel_subset_lateral (half_pos hw) hwr a hp
      have hpclosed := lateral_subset r hlat
      have hu := hdepth none ⟨p.1,hpclosed.1⟩ ⟨p.2,hpclosed.2⟩ hpx
      have hut : p.2 = (t : ℝ) := congrArg Subtype.val hu
      have hpx' : U.map (p.1,t) = (x : X) :=
        (congrArg U.map (show (p.1,(t : ℝ)) = p from Prod.ext rfl hut.symm)).trans hpx
      have hB : IsClosed ((P false).closedStrip ∪ (P true).closedStrip) :=
        ((P false).isCompact_closed_strip (by norm_num : (1/2 : ℝ) ≤ 1)).isClosed.union
          ((P true).isCompact_closed_strip (by norm_num : (1/2 : ℝ) ≤ 1)).isClosed
      exact original_tube_lateral_mem_closure_endpoint_outside U hr hr1 t ht hlat.1 hB
        (hpx' ▸ hxstrips) x hpx'.symm
  · rcases hxcap with hxcap | hxcap
    · exact hcap false hxcap
    · exact hcap true hxcap

end PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
