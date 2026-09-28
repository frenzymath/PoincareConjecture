import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Pieces.OriginalFrontier

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductPieces
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

def removedLongitudinalSlice
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁) (r : ℝ)
    {j : Bool → V2 → X}
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b)) (t : ℝ) : Set X :=
  (U.map '' ((Ioo (-r) r ×ˢ Ioo (-r) r) ×ˢ {t})) ∪
    ⋃ b : Bool, diskStrip (P b) '' ((I ×ˢ Ioo (-1 / 2 : ℝ) (1 / 2)) ×ˢ {t})

theorem isPreconnected_union_of_closure_contact
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsPreconnected A) (hB : IsPreconnected B)
    {x : X} (hxA : x ∈ closure A) (hxB : x ∈ B) : IsPreconnected (A ∪ B) := by
  have hi : IsPreconnected (insert x A) :=
    hA.subset_closure (subset_insert x A) (insert_subset hxA subset_closure)
  have h := hi.union x (mem_insert x A) hxB hB
  have heq : insert x A ∪ B = A ∪ B := by
    ext y
    simp only [mem_union, mem_insert_iff]
    constructor
    · rintro ((rfl | hy) | hy)
      · exact Or.inr hxB
      · exact Or.inl hy
      · exact Or.inr hy
    · exact fun h => h.elim (fun hy => Or.inl (Or.inr hy)) Or.inr
  exact heq ▸ h

theorem isPreconnected_removed_longitudinal_slice
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r w : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {j : Bool → V2 → X}
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
    (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ)
    (hmark : ∀ b, ∀ z ∈ Rim, ∀ s ∈ J,
      (P b).map (z, s) = F b (z, (w / ρ b) * s))
    (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F side (rimArmPoint b t, s) = prescribedArmBand U r (ρ side) 0 1 side b (s, t))
    {t : ℝ} (ht : t ∈ I) :
    IsPreconnected (removedLongitudinalSlice U r P t) := by
  let A := U.map '' ((Ioo (-r) r ×ˢ Ioo (-r) r) ×ˢ {t})
  let B := fun b => diskStrip (P b) '' ((I ×ˢ Ioo (-1 / 2 : ℝ) (1 / 2)) ×ˢ {t})
  have hcl : closure ((Ioo (-r) r ×ˢ Ioo (-r) r) ×ˢ {t}) =
      (Icc (-r) r ×ˢ Icc (-r) r) ×ˢ {t} := by
    rw [closure_prod_eq, closure_prod_eq, closure_Ioo (by linarith : -r ≠ r),
      closure_singleton]
  have hsub : (Icc (-r) r ×ˢ Icc (-r) r) ×ˢ {t} ⊆ tube := by
    intro z hz
    apply closedTube_subset hr1
    exact ⟨hz.1, hz.2 ▸ ht⟩
  have hcont : ContinuousOn U.map (closure ((Ioo (-r) r ×ˢ Ioo (-r) r) ×ˢ {t})) := by
    rw [hcl]
    exact U.pl.continuousOn.mono hsub
  have hA : IsPreconnected A :=
    (((convex_Ioo (-r) r).prod (convex_Ioo (-r) r)).isPreconnected.prod
      isPreconnected_singleton).image U.map (hcont.mono subset_closure)
  have hB (b : Bool) : IsPreconnected (B b) := by
    apply (((convex_Icc (0 : ℝ) 1).prod (convex_Ioo (-1 / 2 : ℝ) (1 / 2))).isPreconnected.prod
      isPreconnected_singleton).image
    exact (diskStrip_properties (P b)).1.continuousOn.mono (by
      intro z hz
      exact ⟨⟨hz.1.1, by linarith [hz.1.2.1], hz.1.2.2.le⟩, hz.2 ▸ ht⟩)
  have hcontact (b : Bool) : ∃ x ∈ closure A, x ∈ B b := by
    let z : C3 := ((r, if b then -r else r), t)
    have hz : z ∈ closure ((Ioo (-r) r ×ˢ Ioo (-r) r) ×ˢ {t}) := by
      rw [hcl]
      refine ⟨⟨⟨by linarith, le_rfl⟩, ?_⟩, rfl⟩
      cases b <;> dsimp [z] <;> constructor <;> linarith
    refine ⟨U.map z, hcont.image_closure (mem_image_of_mem U.map hz), ?_⟩
    refine ⟨((1, 0), t), ⟨⟨by norm_num, by norm_num⟩, rfl⟩, ?_⟩
    have harm := diskStrip_arm (P b) false 0 t
    simp only [Bool.false_eq_true, if_false] at harm
    rw [harm, hmark b _ (rimArmPoint_mem_rim false ht) 0 (by norm_num)]
    simp only [mul_zero]
    rw [harms b false t ht 0 (by norm_num)]
    cases b <;> simp [prescribedArmBand, armCoordinates_apply, originalBandMap,
      bandMap, arcMap, sign, z]
  obtain ⟨x, hxA, hxB⟩ := hcontact false
  obtain ⟨y, hyA, hyB⟩ := hcontact true
  have hAB := isPreconnected_union_of_closure_contact hA (hB false) hxA hxB
  have h := isPreconnected_union_of_closure_contact hAB (hB true)
    (closure_mono subset_union_left hyA) hyB
  have hBool : (⋃ b, B b) = B false ∪ B true := by
    ext x
    simp only [mem_iUnion, Bool.exists_bool, mem_union]
  change IsPreconnected (A ∪ ⋃ b, B b)
  rw [hBool, ← union_assoc]
  exact h

end PoincareConjecture.M76.Dehn.Annuli.ProductPieces
