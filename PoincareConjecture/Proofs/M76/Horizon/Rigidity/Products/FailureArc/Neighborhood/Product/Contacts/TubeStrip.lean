import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Pieces.DiskStrip
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CutGeometry

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductPieces
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "H" => Icc (-(1/2 : ℝ)) (1/2)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

theorem diskStrip_mem_closedTube_iff
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r a : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (ha : 0 < a) (ha1 : a ≤ 1)
    {j : V2 → X} (P : OriginalDiskProduct e (R \ U.map '' openTube r) j)
    (F : V2 × ℝ → X)
    (hmark : ∀ z ∈ Rim, ∀ s ∈ J, P.map (z,s) = F (z,a*s))
    (hlateral : ∀ z ∈ Rim, ∀ s ∈ J,
      F (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    {p : P2} (hp : p ∈ stripBase) {t : ℝ} (ht : t ∈ I) :
    diskStrip P (p,t) ∈ U.map '' closedTube r ↔
      ∃ b : Bool, p.1 = if b then 0 else 1 := by
  have hpD := stripCoordinates_bijOn.1 (show (p,t) ∈ stripBase ×ˢ I from ⟨hp,ht⟩)
  have hs : p.2 ∈ J := ⟨by linarith [hp.2.1],by linarith [hp.2.2]⟩
  have has : a*p.2 ∈ J := by constructor <;> nlinarith [hs.1,hs.2]
  constructor
  · intro hmem
    have hout := (diskStrip_properties P).2.2.1 (show (p,t) ∈ stripBase ×ˢ I from ⟨hp,ht⟩)
    have hlat : diskStrip P (p,t) ∈ U.map '' lateral r :=
      (TubeExterior.OriginalIntervalTube.closedTube_sdiff_openTube U hr hr1).subset ⟨hmem,hout.2⟩
    have hfront : diskStrip P (p,t) ∈ frontier (R \ U.map '' openTube r) := by
      rw [TubeExterior.OriginalIntervalTube.frontier_exterior U hR he hr hr1]
      exact Or.inr hlat
    have hz : CubeCoordinates.fromRectangle (p.1,t) ∈ Rim :=
      (P.proper _ ⟨hpD.1,hs⟩).mp hfront
    have hF : F (CubeCoordinates.fromRectangle (p.1,t),a*p.2) ∈ U.map '' lateral r := by
      rw [← hmark _ hz _ hs]
      exact hlat
    obtain ⟨b,u,hu,hzu⟩ := (hlateral _ hz _ has).mp hF
    refine ⟨b,?_⟩
    have hx := congrFun hzu 0
    cases b <;> simp [CubeCoordinates.fromRectangle,rimArmPoint,sign] at hx ⊢ <;> linarith
  · rintro ⟨b,hb⟩
    have hlat : P.map (rimArmPoint b t,p.2) ∈ U.map '' lateral r := by
      rw [hmark _ (rimArmPoint_mem_rim b ht) _ hs]
      exact (hlateral _ (rimArmPoint_mem_rim b ht) _ has).mpr ⟨b,t,ht,rfl⟩
    have hv : diskStrip P (p,t) = P.map (rimArmPoint b t,p.2) := by
      rw [show p = (if b then 0 else 1,p.2) from Prod.ext hb rfl]
      exact diskStrip_arm P b p.2 t
    rw [hv]
    exact image_mono (lateral_subset r) hlat

theorem tube_diskStrip_eq_iff
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
      F (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    {q p : P2} (hq : q ∈ transverseSquare r) (hp : p ∈ stripBase)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    U.map (q,s) = diskStrip P (p,t) ↔
      ∃ b : Bool, p.1 = (if b then 0 else 1) ∧
        q = arcMap r (b,if side then !b else b) (w*(sign b*p.2)) ∧ s = t := by
  have hwr : w/2 < r := by
    have h := (div_le_iff₀ hρ).mp hwρ
    linarith
  have hedge := diskStrip_prescribed_arms P F U r side hρ hw hwρ hmark harms
  have hband (b : Bool) :
      (arcMap r (b,if side then !b else b) (w*(sign b*p.2)),t) ∈ closedTube r := by
    apply lateral_subset r
    apply band_subset_lateral (by linarith : 0 ≤ w/2) hwr.le (b,if side then !b else b)
    exact ⟨arcMap_mem_footprint (by linarith : 0 ≤ w/2) _ (by
      cases b <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul]
      all_goals constructor <;> nlinarith [hp.2.1,hp.2.2]),ht⟩
  constructor
  · intro heq
    have hmem : diskStrip P (p,t) ∈ U.map '' closedTube r := ⟨(q,s),⟨hq,hs⟩,heq⟩
    obtain ⟨b,hb⟩ := (diskStrip_mem_closedTube_iff U hR he (hρ.trans hρr) hr1
      (div_pos hw hρ) hwρ P F hmark hlateral hp ht).mp hmem
    have hval : diskStrip P (p,t) = originalBandMap U r (b,if side then !b else b)
        (w*(sign b*p.2),t) := by
      rw [show p = (if b then 0 else 1,p.2) from Prod.ext hb rfl]
      exact hedge b t ht p.2 hp.2
    have hinj := (TubeExterior.OriginalIntervalTube.restrict_closedTube U (hρ.trans hρr) hr1).2.1
    have hqt := hinj ⟨hq,hs⟩ (hband b) (heq.trans hval)
    exact ⟨b,hb,congrArg Prod.fst hqt,congrArg Prod.snd hqt⟩
  · rintro ⟨b,hb,hq',hst⟩
    subst s
    rw [hq',show p = (if b then 0 else 1,p.2) from Prod.ext hb rfl]
    exact (hedge b t ht p.2 hp.2).symm

theorem tube_diskStrip_collision_iff
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
      F (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    {q p : P2} (hq : q ∈ transverseSquare r) (hp : p ∈ stripBase)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    U.map (q,s) = diskStrip P (p,t) ↔
      U.map (q,0) = diskStrip P (p,0) ∧ s = t := by
  have h := tube_diskStrip_eq_iff U hR he hρ hρr hr1 hw hwρ P F side
    hmark harms hlateral hq hp hs ht
  have h₀ := tube_diskStrip_eq_iff U hR he hρ hρr hr1 hw hwρ P F side
    hmark harms hlateral hq hp (by norm_num : (0 : ℝ) ∈ I) (by norm_num : (0 : ℝ) ∈ I)
  rw [h,h₀]
  constructor
  · rintro ⟨b,hb,hq,hst⟩
    exact ⟨⟨b,hb,hq,rfl⟩,hst⟩
  · rintro ⟨⟨b,hb,hq,_⟩,hst⟩
    exact ⟨b,hb,hq,hst⟩

end PoincareConjecture.M76.Dehn.Annuli.ProductPieces
