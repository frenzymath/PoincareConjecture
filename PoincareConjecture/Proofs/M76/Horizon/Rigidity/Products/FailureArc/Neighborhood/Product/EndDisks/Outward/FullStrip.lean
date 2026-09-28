import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Pieces.OriginalFrontier



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

omit [T2Space X] in
theorem continuousOn_full_diskStrip_slice
    {Q : Set X} {j : V2 → X} (P : OriginalDiskProduct e Q j)
    {t : ℝ} (ht : t ∈ I) : ContinuousOn (fun p : P2 => diskStrip P (p, t)) (I ×ˢ J) := by
  apply P.polyhedral.continuousOn.comp
    (f := fun p : P2 => (CubeCoordinates.fromRectangle (p.1, t), p.2))
  · exact (((CubeCoordinates.fromRectangle_finitePL.continuousOn).comp
      (continuous_fst.prodMk continuous_const).continuousOn
      (fun p hp => ⟨hp.1, ht⟩)).prodMk continuous_snd.continuousOn)
  · intro p hp
    refine ⟨(CubeCoordinates.toRectangle_mem_iff _).mp ?_, hp.2⟩
    rw [CubeCoordinates.toRectangle_fromRectangle]
    exact ⟨hp.1, ht⟩

theorem full_diskStrip_mem_closedTube_iff
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r a : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (ha : 0 < a) (ha1 : a ≤ 1)
    {j : V2 → X} (P : OriginalDiskProduct e (R \ U.map '' openTube r) j)
    (F : V2 × ℝ → X)
    (hmark : ∀ z ∈ Rim, ∀ s ∈ J, P.map (z, s) = F (z, a * s))
    (hlateral : ∀ z ∈ Rim, ∀ s ∈ J,
      F (z, s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    {p : P2} (hp : p ∈ I ×ˢ J) {t : ℝ} (ht : t ∈ I) :
    diskStrip P (p, t) ∈ U.map '' closedTube r ↔
      ∃ b : Bool, p.1 = if b then 0 else 1 := by
  have hzD : CubeCoordinates.fromRectangle (p.1, t) ∈ Disk :=
    (CubeCoordinates.toRectangle_mem_iff _).mp
      (by rw [CubeCoordinates.toRectangle_fromRectangle]; exact ⟨hp.1, ht⟩)
  have has : a * p.2 ∈ J := by constructor <;> nlinarith [hp.2.1, hp.2.2]
  constructor
  · intro hmem
    have hout : diskStrip P (p, t) ∈ R \ U.map '' openTube r := P.inside ⟨hzD, hp.2⟩
    have hlat := (TubeExterior.OriginalIntervalTube.closedTube_sdiff_openTube U hr hr1).subset
      ⟨hmem, hout.2⟩
    have hfront : diskStrip P (p, t) ∈ frontier (R \ U.map '' openTube r) := by
      rw [TubeExterior.OriginalIntervalTube.frontier_exterior U hR he hr hr1]
      exact Or.inr hlat
    have hz : CubeCoordinates.fromRectangle (p.1, t) ∈ Rim :=
      (P.proper _ ⟨hzD, hp.2⟩).mp hfront
    have hF : F (CubeCoordinates.fromRectangle (p.1, t), a * p.2) ∈
        U.map '' lateral r := by
      rw [← hmark _ hz _ hp.2]
      exact hlat
    obtain ⟨b, u, hu, hzu⟩ := (hlateral _ hz _ has).mp hF
    refine ⟨b, ?_⟩
    have hx := congrFun hzu 0
    cases b <;> simp [CubeCoordinates.fromRectangle, rimArmPoint, sign] at hx ⊢ <;> linarith
  · rintro ⟨b, hb⟩
    have hlat : P.map (rimArmPoint b t, p.2) ∈ U.map '' lateral r := by
      rw [hmark _ (rimArmPoint_mem_rim b ht) _ hp.2]
      exact (hlateral _ (rimArmPoint_mem_rim b ht) _ has).mpr ⟨b, t, ht, rfl⟩
    have hv : diskStrip P (p, t) = P.map (rimArmPoint b t, p.2) := by
      rw [show p = (if b then 0 else 1, p.2) from Prod.ext hb rfl]
      exact diskStrip_arm P b p.2 t
    rw [hv]
    exact image_mono (lateral_subset r) hlat

theorem full_diskStrip_mem_original_frontier_iff
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r ρ w : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr1 : r ≤ 1)
    (hw : 0 < w) (hwρ : w / ρ ≤ 1)
    {j : V2 → X} (P : OriginalDiskProduct e (R \ U.map '' openTube r) j)
    (F : V2 × ℝ → X) (side : Bool)
    (hmark : ∀ z ∈ Rim, ∀ s ∈ J, P.map (z, s) = F (z, (w / ρ) * s))
    (harms : ∀ b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F (rimArmPoint b t, s) = prescribedArmBand U r ρ 0 1 side b (s, t))
    (hlateral : ∀ z ∈ Rim, ∀ s ∈ J,
      F (z, s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    {p : P2} (hp : p ∈ I ×ˢ J) {t : ℝ} (ht : t ∈ I) :
    diskStrip P (p, t) ∈ frontier R ↔ t = 0 ∨ t = 1 := by
  have hr := hρ.trans hρr
  have ha : 0 < w / ρ := div_pos hw hρ
  have has : (w / ρ) * p.2 ∈ J := by constructor <;> nlinarith [hp.2.1, hp.2.2]
  have harm (b : Bool) (hb : p.1 = if b then 0 else 1) :
      diskStrip P (p, t) ∈ frontier R ↔ t = 0 ∨ t = 1 := by
    rw [show p = (if b then 0 else 1, p.2) from Prod.ext hb rfl, diskStrip_arm,
      hmark _ (rimArmPoint_mem_rim b ht) _ hp.2, harms b t ht _ has]
    exact (prescribedArmBand_properties U hR he hρ hρr hr1
      (Or.inl ⟨rfl, rfl⟩) side b).2.2.2.2.2 _ ⟨has, ht⟩
  have hout : diskStrip P (p, t) ∈ R \ U.map '' openTube r :=
    P.inside ⟨(CubeCoordinates.toRectangle_mem_iff _).mp
      (by change CubeCoordinates.toRectangle (CubeCoordinates.fromRectangle (p.1, t)) ∈ _
          rw [CubeCoordinates.toRectangle_fromRectangle]
          exact ⟨hp.1, ht⟩), hp.2⟩
  constructor
  · intro hf
    have hfQ : diskStrip P (p, t) ∈ frontier (R \ U.map '' openTube r) := by
      rw [TubeExterior.OriginalIntervalTube.frontier_exterior U hR he hr hr1]
      exact Or.inl ⟨hf, hout.2⟩
    have hrect := ((capRectangle_properties P hp.2).2.2.2.2 (p.1, t) ⟨hp.1, ht⟩).mp hfQ
    rw [frontier_prod_eq, isClosed_Icc.closure_eq, frontier_Icc zero_le_one] at hrect
    rcases hrect with ⟨_, hends⟩ | ⟨hends, _⟩
    · simpa only [mem_insert_iff, mem_singleton_iff] using hends
    · rcases hends with hx | hx
      · exact (harm true hx).mp hf
      · exact (harm false hx).mp hf
  · intro htend
    have hrect : (p.1, t) ∈ frontier (I ×ˢ I : Set P2) := by
      rw [frontier_prod_eq, isClosed_Icc.closure_eq, frontier_Icc zero_le_one]
      exact Or.inl ⟨hp.1, by simpa only [mem_insert_iff, mem_singleton_iff] using htend⟩
    have hfQ := ((capRectangle_properties P hp.2).2.2.2.2 (p.1, t) ⟨hp.1, ht⟩).mpr hrect
    rw [TubeExterior.OriginalIntervalTube.frontier_exterior U hR he hr hr1] at hfQ
    rcases hfQ with hold | hlat
    · exact hold.1
    · obtain ⟨b, hb⟩ := (full_diskStrip_mem_closedTube_iff U hR he hr hr1 ha hwρ
        P F hmark hlateral hp ht).mp (image_mono (lateral_subset r) hlat)
      exact (harm b hb).mpr htend

end PoincareConjecture.M76.Dehn.Annuli.ProductPieces
