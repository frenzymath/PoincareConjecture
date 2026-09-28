import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.ConnectedRemoval



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

theorem diskStrip_open_image
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e Q j) :
    diskStrip P '' ((I ×ˢ Ioo (-1 / 2 : ℝ) (1 / 2)) ×ˢ I) = P.openStrip := by
  change (P.map ∘ stripCoordinates) '' _ = P.map '' _
  rw [image_comp]
  congr 1
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(CubeCoordinates.toRectangle_mem_iff _).mp ?_, ?_⟩
    · simpa only [stripCoordinates, CubeCoordinates.toRectangle_fromRectangle] using
        (show (y.1.1, y.2) ∈ I ×ˢ I from ⟨hy.1.1, hy.2⟩)
    · simpa only [stripCoordinates, neg_div] using hy.1.2
  · intro hz
    have hrect := CubeCoordinates.toRectangle_bijOn.1 hz.1
    refine ⟨(((CubeCoordinates.toRectangle z.1).1, z.2),
      (CubeCoordinates.toRectangle z.1).2), ⟨⟨hrect.1, ?_⟩, hrect.2⟩, ?_⟩
    · simpa only [neg_div] using hz.2
    · change (CubeCoordinates.fromRectangle (CubeCoordinates.toRectangle z.1), z.2) = z
      rw [CubeCoordinates.fromRectangle_toRectangle]

private theorem image_inter_frontier_of_depth
    {X B : Type*} [TopologicalSpace X] {R : Set X} (f : B × ℝ → X) (A : Set B)
    (hfront : ∀ x ∈ A, ∀ t ∈ I, f (x, t) ∈ frontier R ↔ t = 0 ∨ t = 1) :
    (f '' (A ×ˢ I)) ∩ frontier R = (f '' (A ×ˢ {0})) ∪ (f '' (A ×ˢ {1})) := by
  ext z
  constructor
  · rintro ⟨⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩, hf⟩
    rcases (hfront x hx t ht).mp hf with h | h
    · exact Or.inl ⟨(x, t), ⟨hx, h⟩, rfl⟩
    · exact Or.inr ⟨(x, t), ⟨hx, h⟩, rfl⟩
  · rintro (⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ | ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩)
    · have h : t = 0 := ht
      subst t
      exact ⟨⟨(x, 0), ⟨hx, by norm_num⟩, rfl⟩,
        (hfront x hx 0 (by norm_num)).mpr (Or.inl rfl)⟩
    · have h : t = 1 := ht
      subst t
      exact ⟨⟨(x, 1), ⟨hx, by norm_num⟩, rfl⟩,
        (hfront x hx 1 (by norm_num)).mpr (Or.inr rfl)⟩

theorem removed_neighborhood_inter_original_frontier
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r w : ℝ} (hw : 0 < w) (hr1 : r ≤ 1)
    {j : Bool → V2 → X}
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
    (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ)
    (hρ : ∀ b, 0 < ρ b) (hρr : ∀ b, ρ b < r) (hwρ : ∀ b, w / ρ b ≤ 1)
    (hmark : ∀ b, ∀ z ∈ Rim, ∀ s ∈ J,
      (P b).map (z, s) = F b (z, (w / ρ b) * s))
    (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F side (rimArmPoint b t, s) = prescribedArmBand U r (ρ side) 0 1 side b (s, t))
    (hlateral : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
      F side (z, s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t) :
    (U.map '' openTube r ∪ (P false).openStrip ∪ (P true).openStrip) ∩ frontier R =
      removedLongitudinalSlice U r P 0 ∪ removedLongitudinalSlice U r P 1 := by
  have hU := image_inter_frontier_of_depth U.map (Ioo (-r) r ×ˢ Ioo (-r) r)
    (fun x hx t ht => U.frontier_iff (x, t)
      (closedTube_subset hr1 ⟨⟨⟨hx.1.1.le, hx.1.2.le⟩, ⟨hx.2.1.le, hx.2.2.le⟩⟩, ht⟩))
  have hP (b : Bool) := image_inter_frontier_of_depth (diskStrip (P b))
    (I ×ˢ Ioo (-1 / 2 : ℝ) (1 / 2)) (fun x hx t ht =>
      diskStrip_mem_original_frontier_iff U hR he (hρ b) (hρr b) hr1 hw (hwρ b)
        (P b) (F b) b (hmark b) (harms b) (hlateral b)
        ⟨hx.1, by linarith [hx.2.1], hx.2.2.le⟩ ht)
  rw [union_inter_distrib_right, union_inter_distrib_right, ← diskStrip_open_image (P false),
    ← diskStrip_open_image (P true)]
  change _ ∪ _ ∪ _ = _
  have hU' : (U.map '' openTube r) ∩ frontier R =
      U.map '' ((Ioo (-r) r ×ˢ Ioo (-r) r) ×ˢ {0}) ∪
        U.map '' ((Ioo (-r) r ×ˢ Ioo (-r) r) ×ˢ {1}) := by
    simpa only [openTube, transverseSquare, interior_prod_eq, interior_Icc] using hU
  rw [hU', hP false, hP true]
  ext x
  simp only [removedLongitudinalSlice, mem_union, mem_iUnion, Bool.exists_bool]
  tauto

end PoincareConjecture.M76.Dehn.Annuli.ProductPieces
