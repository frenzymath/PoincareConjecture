import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.OriginalNormalizedResolutionFibers
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.Counts

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "D2" => closedBall (0 : V2) 1

variable {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X F}
  {f : V2 → X} {Z : Set X} {base : Z} {G : Subgroup (FundamentalGroup Z base)}
  {c : Bool → P2 → V2} {τ : C3 → X}
  {D : OriginalResolutionWordExclusionData f Z base G c τ (1 / 4)}

theorem OriginalNormalizedResolutionPairData.images_subset_original
    (P : OriginalNormalizedResolutionPairData e D) :
    P.gU '' D2 ⊆ f '' D2 ∪ τ '' tube ∧ P.gV '' D2 ⊆ f '' D2 ∪ τ '' tube := by
  have hAS : D.A ⊆ D2 := fun x hx ↦ D.cover.subset (Or.inl (Or.inl (Or.inl hx)))
  have hMS : D.M ⊆ D2 := fun x hx ↦ D.cover.subset (Or.inl (Or.inl (Or.inr hx)))
  have hCS : D.C ⊆ D2 := fun x hx ↦ D.cover.subset (Or.inl (Or.inr hx))
  have hreplace (alternatePair positive : Bool) :
      (τ ∘ tubeArmOrientation D.s0 D.s1) ''
        (resolutionMap (1 / 4) alternatePair positive '' source) ⊆ f '' D2 ∪ τ '' tube := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    apply Or.inr
    exact ⟨tubeArmOrientation D.s0 D.s1 (resolutionMap (1 / 4) alternatePair positive x),
      (tubeArmOrientation_mem_tube D.s0 D.s1 _).mpr
        (resolutionMap_mapsTo_tube (by norm_num) alternatePair positive hx), rfl⟩
  constructor
  · rw [P.imageU]
    exact union_subset (union_subset ((image_mono hAS).trans subset_union_left)
      (hreplace false true)) ((image_mono hCS).trans subset_union_left)
  · rw [P.imageV]
    exact union_subset (union_subset (union_subset (union_subset
      ((image_mono hAS).trans subset_union_left) (hreplace true false))
      ((image_mono hMS).trans subset_union_left)) (hreplace true true))
      ((image_mono hCS).trans subset_union_left)

theorem OriginalNormalizedResolutionPairData.region_properness
    (P : OriginalNormalizedResolutionPairData e D) {R : Set X}
    (hfR : MapsTo f D2 R) (hτR : MapsTo τ tube R)
    (hffrontier : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    (hτfrontier : ∀ z ∈ tube, τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1)
    (hfZ : ∀ x ∈ D2, f x ∈ Z ↔ x ∈ Q2)
    (hτZ : ∀ z ∈ tube, τ z ∈ Z ↔ z.2 = 0 ∨ z.2 = 1) :
    MapsTo P.gU D2 R ∧ MapsTo P.gV D2 R ∧
      (∀ x ∈ D2, P.gU x ∈ frontier R ↔ x ∈ Q2) ∧
      (∀ x ∈ D2, P.gV x ∈ frontier R ↔ x ∈ Q2) := by
  have hcommon (y : X) (hy : y ∈ f '' D2 ∪ τ '' tube) :
      y ∈ R ∧ (y ∈ frontier R ↔ y ∈ Z) := by
    rcases hy with ⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩
    · exact ⟨hfR hx, (hffrontier x hx).trans (hfZ x hx).symm⟩
    · exact ⟨hτR hz, (hτfrontier z hz).trans (hτZ z hz).symm⟩
  have hU (x : V2) (hx : x ∈ D2) :=
    hcommon (P.gU x) (P.images_subset_original.1 ⟨x, hx, rfl⟩)
  have hV (x : V2) (hx : x ∈ D2) :=
    hcommon (P.gV x) (P.images_subset_original.2 ⟨x, hx, rfl⟩)
  exact ⟨fun x hx ↦ (hU x hx).1, fun x hx ↦ (hV x hx).1,
    fun x hx ↦ (hU x hx).2.trans (P.properU x hx),
    fun x hx ↦ (hV x hx).2.trans (P.properV x hx)⟩

theorem RetainedSquareMapFacts.unique_other_point
    {Y : Type*} {f g : V2 → Y} {S : Set V2} {j : S → V2}
    (facts : RetainedSquareMapFacts f g S j)
    (hold : ∀ x ∈ D2, ∀ y ∈ D2, ∀ z ∈ D2,
      f x = f y → f x = f z → x ≠ y → x ≠ z → y = z) :
    ∀ x ∈ D2, ∀ y ∈ D2, ∀ z ∈ D2,
      g x = g y → g x = g z → x ≠ y → x ≠ z → y = z := by
  intro x hx y hy z hz hxy hxz hnxy hnxz
  have hxy' : (x, y) ∈
      {v : V2 × V2 | v.1 ∈ D2 ∧ v.2 ∈ D2 ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} :=
    ⟨hx, hy, hxy, hnxy⟩
  have hxz' : (x, z) ∈
      {v : V2 × V2 | v.1 ∈ D2 ∧ v.2 ∈ D2 ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} :=
    ⟨hx, hz, hxz, hnxz⟩
  rw [facts.double_relation] at hxy' hxz'
  obtain ⟨⟨a, b⟩, ⟨hab, hnab⟩, hpairAB⟩ := hxy'
  obtain ⟨⟨a', d⟩, ⟨had, hnad⟩, hpairAD⟩ := hxz'
  have hja : j a = x := congrArg Prod.fst hpairAB
  have hjb : j b = y := congrArg Prod.snd hpairAB
  have hja' : j a' = x := congrArg Prod.fst hpairAD
  have hjd : j d = z := congrArg Prod.snd hpairAD
  have haa : a' = a := facts.injective (hja'.trans hja.symm)
  subst a'
  have hbd : (b : V2) = d := hold a (facts.old_subset a.property)
    b (facts.old_subset b.property) d (facts.old_subset d.property) hab had hnab hnad
  exact hjb.symm.trans ((congrArg j (Subtype.ext hbd)).trans hjd)

theorem OriginalNormalizedResolutionPairData.unique_other_points
    (P : OriginalNormalizedResolutionPairData e D)
    (hτ : InjOn τ tube)
    (hfull : D2 ∩ f ⁻¹' (τ '' tube) = (c false '' source) ∪ (c true '' source))
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfZ : ∀ x ∈ D2, f x ∈ Z ↔ x ∈ Q2)
    (partner : doubleLocusOn f D2 → doubleLocusOn f D2)
    (hunique : ∀ (x : doubleLocusOn f D2) (y : V2), y ∈ D2 →
      f x = f y → (x : V2) ≠ y → y = (partner x : V2)) :
    (∀ x ∈ D2, ∀ y ∈ D2, ∀ z ∈ D2,
      P.gU x = P.gU y → P.gU x = P.gU z → x ≠ y → x ≠ z → y = z) ∧
    (∀ x ∈ D2, ∀ y ∈ D2, ∀ z ∈ D2,
      P.gV x = P.gV y → P.gV x = P.gV z → x ≠ y → x ≠ z → y = z) := by
  have hold : ∀ x ∈ D2, ∀ y ∈ D2, ∀ z ∈ D2,
      f x = f y → f x = f z → x ≠ y → x ≠ z → y = z := by
    intro x hx y hy z hz hxy hxz hnxy hnxz
    let x' : doubleLocusOn f D2 := ⟨x, hx, y, hy, hxy, hnxy⟩
    exact (hunique x' y hy hxy hnxy).trans (hunique x' z hz hxz hnxz).symm
  obtain ⟨factsU, factsV⟩ := P.retained_fibers hτ hfull h0 h1 hfZ
  exact ⟨factsU.unique_other_point hold, factsV.unique_other_point hold⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
