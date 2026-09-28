import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.Matching.CapSides
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CornerBands.OriginalGeometry
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CutGeometry



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

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

theorem lateral_inter_openStrip
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r ρ w : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr1 : r ≤ 1)
    (hw : 0 < w) (hwρ : w/ρ ≤ 1)
    {j : V2 → X} (P : OriginalDiskProduct e (R \ U.map '' openTube r) j)
    (F : V2 × ℝ → X) (side : Bool)
    (hmark : ∀ z ∈ Rim, ∀ s ∈ J, P.map (z,s) = F (z,(w/ρ)*s))
    (harms : ∀ b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F (rimArmPoint b t,s) = prescribedArmBand U r ρ 0 1 side b (s,t))
    (hlateral : ∀ z ∈ Rim, ∀ s ∈ J,
      F (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t) :
    (U.map '' lateral r) ∩ P.openStrip =
      ⋃ b : Bool, U.map '' openBand r (w/2) (b,if side then !b else b) := by
  have hwr : w/2 < r := by
    have h := (div_le_iff₀ hρ).mp hwρ
    linarith
  have hedge := capRectangle_common_width_arm_edges P F U r side hρ hw hwρ hmark harms
  have hpoint (b : Bool) (t : ℝ) (ht : t ∈ I) (s : ℝ) (hs : s ∈ J) :
      P.map (rimArmPoint b t,s) =
        originalBandMap U r (b,if side then !b else b) (w*(sign b*s),t) := by
    rw [← capRectangle_arm_parameter]
    exact hedge b t ht s hs
  have hbandlat (i : Bool × Bool) : openBand r (w/2) i ⊆ lateral r :=
    (prod_mono (openFootprint_subset r (w/2) i) Subset.rfl).trans
      (band_subset_lateral (by linarith : 0 ≤ w/2) hwr.le i)
  ext x
  constructor
  · rintro ⟨hxlat,p,hp,rfl⟩
    have hs : p.2 ∈ J := ⟨by linarith [hp.2.1],by linarith [hp.2.2]⟩
    have hfront : P.map p ∈ frontier (R \ U.map '' openTube r) := by
      rw [TubeExterior.OriginalIntervalTube.frontier_exterior U hR he (hρ.trans hρr) hr1]
      exact Or.inr hxlat
    have hprim := (P.proper p ⟨hp.1,hs⟩).mp hfront
    have hscale : (w/ρ)*p.2 ∈ J := by
      have ha : 0 < w/ρ := div_pos hw hρ
      constructor <;> nlinarith [hs.1,hs.2]
    have hF : F (p.1,(w/ρ)*p.2) ∈ U.map '' lateral r := by
      rw [← hmark _ hprim _ hs]
      exact hxlat
    obtain ⟨b,t,ht,hpt⟩ := (hlateral _ hprim _ hscale).mp hF
    have hv : P.map p = originalBandMap U r (b,if side then !b else b)
        (w*(sign b*p.2),t) := by
      rw [show p = (rimArmPoint b t,p.2) from Prod.ext hpt rfl]
      exact hpoint b t ht p.2 hs
    rw [hv]
    refine mem_iUnion.mpr ⟨b,bandMap r (b,if side then !b else b) (w*(sign b*p.2),t),?_,rfl⟩
    apply (bandMap_open_image (by linarith : 0 ≤ w/2) _).subset
    refine ⟨(w*(sign b*p.2),t),⟨?_,ht⟩,rfl⟩
    cases b <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul]
    all_goals constructor <;> nlinarith [hp.2.1,hp.2.2]
  · intro hx
    obtain ⟨b,z,hz,rfl⟩ := mem_iUnion.mp hx
    refine ⟨⟨z,hbandlat _ hz,rfl⟩,?_⟩
    obtain ⟨q,hq,hqval⟩ := (bandMap_open_image (by linarith : 0 ≤ w/2) _).symm.subset hz
    let s : ℝ := sign b*q.1/w
    have hs : s ∈ Ioo (-(1/2 : ℝ)) (1/2) := by
      change -(1/2 : ℝ) < sign b*q.1/w ∧ sign b*q.1/w < 1/2
      rw [lt_div_iff₀ hw,div_lt_iff₀ hw]
      cases b <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul]
      all_goals constructor <;> linarith [hq.1.1,hq.1.2]
    have hsJ : s ∈ J := ⟨by linarith [hs.1],by linarith [hs.2]⟩
    have hqeq : w*(sign b*s)=q.1 := by
      dsimp [s]
      cases b <;> simp [sign] <;> field_simp
    refine ⟨(rimArmPoint b q.2,s),⟨sphere_subset_closedBall (rimArmPoint_mem_rim b hq.2),hs⟩,?_⟩
    rw [hpoint b q.2 hq.2 s hsJ,hqeq]
    exact congrArg U.map hqval

theorem lateral_sdiff_two_openStrips
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
      F side (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t) :
    (U.map '' lateral r) \ ((P false).openStrip ∪ (P true).openStrip) =
      ⋃ i : Bool × Bool, U.map '' panel r (w/2) i := by
  have hcut (side : Bool) := lateral_inter_openStrip U hR he (hρ side) (hρr side) hr1
    hw (hwρ side) (P side) (F side) side (hmark side) (harms side) (hlateral side)
  have hremoved : (U.map '' lateral r) ∩ ((P false).openStrip ∪ (P true).openStrip) =
      ⋃ i : Bool × Bool, U.map '' openBand r (w/2) i := by
    rw [inter_union_distrib_left,hcut false,hcut true]
    ext x
    simp only [mem_union,mem_iUnion,Prod.exists,Bool.exists_bool,Bool.false_eq_true,
      if_false,if_true,Bool.not_false,Bool.not_true]
    tauto
  have hwr : w/2 < r := by
    have h := (div_le_iff₀ (hρ false)).mp (hwρ false)
    linarith [hρr false]
  rw [← (original_lateral_decomposition U (by linarith : 0 < w/2) hwr hr1).2.1,
    ← hremoved]
  ext x
  simp only [mem_sdiff,mem_inter_iff]
  tauto

end PoincareConjecture.M76.Dehn.Annuli.BoundaryAssembly
