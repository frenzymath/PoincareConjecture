import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.OriginalResolution
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.OriginalNormalizedResolutionFibers
import Mathlib.Topology.Homeomorph.Lemmas










set_option autoImplicit false

open Set Metric Topology Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1



structure RetainedSourceOpenHomeomorph {X : Type*} (f g : V2 → X)
    (K : Set V2) (j : K → V2) where
  source : Set V2
  target : Set V2
  source_subset : source ⊆ K
  target_subset : target ⊆ D2
  source_open : IsOpen ((Subtype.val : D2 → V2) ⁻¹' source)
  target_open : IsOpen ((Subtype.val : D2 → V2) ⁻¹' target)
  homeomorph : source ≃ₜ target
  value : ∀ x : source, (homeomorph x : V2) = j ⟨x, source_subset x.property⟩
  keep : ∀ x : source, g (homeomorph x) = f x
  boundary : ∀ x : source, (homeomorph x : V2) ∈ Q2 ↔ (x : V2) ∈ Q2
  contains : ∀ x : K, (x : V2) ∈ doubleLocusOn f D2 → (x : V2) ∈ source



theorem RetainedSquareMapFacts.nonempty_open_source_restriction
    {X : Type*} {f g : V2 → X} {K B C : Set V2} {j : K → V2}
    (facts : RetainedSquareMapFacts f g K j)
    (hK : IsCompact K) (hB : IsClosed B) (hC : IsClosed C)
    (holdcover : D2 ⊆ K ∪ B) (hnewcover : D2 ⊆ range j ∪ C)
    (hcontact : ∀ x : K, j x ∈ C → (x : V2) ∈ B)
    (havoid : ∀ x : K, (x : V2) ∈ doubleLocusOn f D2 → (x : V2) ∉ B) :
    Nonempty (RetainedSourceOpenHomeomorph f g K j) := by
  let U : Set V2 := D2 \ B
  have hUK : U ⊆ K := fun x hx ↦ (holdcover hx.1).resolve_right hx.2
  let J : U → V2 := fun x ↦ j ⟨x, hUK x.property⟩
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hj : IsClosedEmbedding j := facts.continuous.isClosedEmbedding facts.injective
  have hJ : IsEmbedding J := hj.isEmbedding.comp (IsEmbedding.inclusion hUK)
  have hseam : IsClosed (j '' ((Subtype.val : K → V2) ⁻¹' B)) :=
    hj.isClosedMap _ (hB.preimage continuous_subtype_val)
  have hrange : range J = D2 \ (C ∪ j '' ((Subtype.val : K → V2) ⁻¹' B)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨facts.mapsTo _, ?_⟩
      rintro (hc | ⟨z, hz, heq⟩)
      · exact x.property.2 (hcontact _ hc)
      · have heq' : z = ⟨x, hUK x.property⟩ := facts.injective heq
        exact x.property.2 ((congrArg (fun t : K ↦ (t : V2) ∈ B) heq').mp hz)
    · rintro ⟨hy, hoff⟩
      rcases hnewcover hy with ⟨x, rfl⟩ | hc
      · have hxB : (x : V2) ∉ B := fun hx ↦ hoff (Or.inr ⟨x, hx, rfl⟩)
        exact ⟨⟨x, facts.old_subset x.property, hxB⟩, rfl⟩
      · exact False.elim (hoff (Or.inl hc))
  refine ⟨⟨U, range J, hUK, ?_, ?_, ?_, hJ.toHomeomorph, ?_, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨x, rfl⟩
    exact facts.mapsTo _
  · have heq : (Subtype.val : D2 → V2) ⁻¹' U =
        ((Subtype.val : D2 → V2) ⁻¹' B)ᶜ := by
      ext x
      exact and_iff_right x.property
    rw [heq]
    exact (hB.preimage continuous_subtype_val).isOpen_compl
  · have heq : (Subtype.val : D2 → V2) ⁻¹' range J =
        ((Subtype.val : D2 → V2) ⁻¹' (C ∪ j '' ((Subtype.val : K → V2) ⁻¹' B)))ᶜ := by
      rw [hrange]
      ext x
      exact and_iff_right x.property
    rw [heq]
    exact ((hC.union hseam).preimage continuous_subtype_val).isOpen_compl
  · intro x
    rfl
  · intro x
    exact facts.keep _
  · intro x
    exact facts.boundary _
  · intro x hx
    exact ⟨facts.old_subset x.property, havoid x hx⟩



theorem RetainedSourceOpenHomeomorph.contains_new_double
    {X : Type*} {f g : V2 → X} {K : Set V2} {j : K → V2}
    (H : RetainedSourceOpenHomeomorph f g K j)
    (facts : RetainedSquareMapFacts f g K j) :
    doubleLocusOn g D2 ⊆ H.target := by
  intro y hy
  obtain ⟨x, ⟨z, hxz, hne⟩, rfl⟩ := facts.double_locus.subset hy
  have hx : (x : V2) ∈ H.source := H.contains x
    ⟨facts.old_subset x.property, z, facts.old_subset z.property, hxz, hne⟩
  rw [← H.value ⟨x, hx⟩]
  exact (H.homeomorph ⟨x, hx⟩).property

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

variable {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X F}
  {f : V2 → X} {Z : Set X} {base : Z} {G : Subgroup (FundamentalGroup Z base)}
  {c : Bool → P2 → V2} {τ : C3 → X}
  {D : OriginalResolutionWordExclusionData f Z base G c τ (1 / 4)}




theorem OriginalNormalizedResolutionPairData.nonempty_retained_source_germs
    (P : OriginalNormalizedResolutionPairData e D)
    (hcPL : ∀ i, FinitePiecewiseAffineOn (c i) source)
    (hci : ∀ i, InjOn (c i) source) (hcS : ∀ i, MapsTo (c i) source D2)
    (hdisj : Disjoint (c false '' source) (c true '' source))
    (hτ : InjOn τ tube)
    (hfull : D2 ∩ f ⁻¹' (τ '' tube) = (c false '' source) ∪ (c true '' source))
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfZ : ∀ x ∈ D2, f x ∈ Z ↔ x ∈ Q2) :
    Nonempty (RetainedSourceOpenHomeomorph f P.gU (D.A ∪ D.C) P.retainedUpperCopy) ∧
    Nonempty (RetainedSourceOpenHomeomorph f P.gV ((D.A ∪ D.M) ∪ D.C)
      P.retainedAlternateCopy) := by
  obtain ⟨factsU, factsV⟩ := P.retained_fibers hτ hfull h0 h1 hfZ
  have hsource : IsCompact source := isCompact_Icc.prod isCompact_Icc
  have : CompactSpace source := isCompact_iff_compactSpace.mp hsource
  let B : Set V2 := (c false '' source) ∪ (c true '' source)
  have hB : IsClosed B := ((hsource.image_of_continuousOn (hcPL false).continuousOn).union
    (hsource.image_of_continuousOn (hcPL true).continuousOn)).isClosed
  have hcenters := original_strip_centers_disjoint_exteriors c hci D.s0 D.s1
    (by simpa only [inter_comm] using D.strip0A) D.oppositeA.inter_eq
    (by simpa only [inter_comm] using D.strip0M)
    (by simpa only [inter_comm] using D.strip1M) D.oppositeC.inter_eq
    (by simpa only [inter_comm] using D.strip1C)
  have havoid (x : ((D.A ∪ D.M) ∪ D.C : Set V2))
      (hx : (x : V2) ∈ doubleLocusOn f D2) : (x : V2) ∉ B := by
    intro hxB
    rcases (original_double_locus_inter_strips c hcS hdisj hτ hfull h0 h1).subset
        ⟨hx, hxB⟩ with hfalse | htrue
    · exact disjoint_left.mp hcenters.1 hfalse x.property
    · exact disjoint_left.mp hcenters.2 htrue x.property
  have hsmall : D.A ∪ D.C ⊆ (D.A ∪ D.M) ∪ D.C :=
    union_subset (subset_union_left.trans subset_union_left) subset_union_right
  have hreplace (alternatePair positive : Bool) (x : source) :
      (τ ∘ tubeArmOrientation D.s0 D.s1) (resolutionMap (1 / 4) alternatePair positive x)
        ∈ τ '' tube := by
    exact ⟨_, (tubeArmOrientation_mem_tube D.s0 D.s1 _).mpr
      (resolutionMap_mapsTo_tube (by norm_num) alternatePair positive x.property), rfl⟩
  have hrU : range P.retainedUpperCopy = range P.sourceU.jA ∪ range P.sourceU.jC :=
    joinSourceCopies_range D.disjointAC _ _
  have hrV : range P.retainedAlternateCopy =
      (range P.sourceV.jA ∪ range P.sourceV.jM) ∪ range P.sourceV.jC := by
    change range (joinSourceCopies _ _ _) = _
    rw [joinSourceCopies_range, joinSourceCopies_range]
  constructor
  · apply factsU.nonempty_open_source_restriction
      (hK := D.diskA.isCompact.union D.diskC.isCompact)
      (B := B ∪ D.M) (C := range P.sourceU.jS)
      (hB := hB.union D.diskM.isCompact.isClosed)
      (hC := (isCompact_range P.sourceU.embeddings.2.1.continuous).isClosed)
    · intro x hx
      rcases D.cover.symm.subset hx with ((ha | hm) | hc) | hs
      · exact Or.inl (Or.inl ha)
      · exact Or.inr (Or.inr hm)
      · exact Or.inl (Or.inr hc)
      · exact Or.inr (Or.inl hs)
    · rw [hrU]
      intro x hx
      rcases P.sourceU.cover.symm.subset hx with (ha | hs) | hc
      · exact Or.inl (Or.inl ha)
      · exact Or.inr hs
      · exact Or.inl (Or.inr hc)
    · rintro x ⟨y, hy⟩
      apply Or.inl
      apply hfull.subset
      refine ⟨factsU.old_subset x.property, ?_⟩
      change f x ∈ τ '' tube
      rw [← factsU.keep x, ← hy]
      have hk := P.sourceU.keepS y
      change P.gU (P.sourceU.jS y) = _ at hk
      rw [hk]
      exact hreplace false true y
    · intro x hx
      rintro (hxB | hxM)
      · exact havoid ⟨x, hsmall x.property⟩ hx hxB
      · exact disjoint_left.mp
          (disjoint_union_left.mpr ⟨D.disjointAM, D.disjointMC.symm⟩) x.property hxM
  · apply factsV.nonempty_open_source_restriction
      (hK := (D.diskA.isCompact.union D.diskM.isCompact).union D.diskC.isCompact)
      (B := B) (C := range P.sourceV.jL ∪ range P.sourceV.jR) (hB := hB)
      (hC := ((isCompact_range P.sourceV.embeddings.2.1.continuous).union
        (isCompact_range P.sourceV.embeddings.2.2.2.1.continuous)).isClosed)
    · exact D.cover.symm.subset
    · rw [hrV]
      intro x hx
      rcases P.sourceV.cover.symm.subset hx with (((ha | hl) | hm) | hr) | hc
      · exact Or.inl (Or.inl (Or.inl ha))
      · exact Or.inr (Or.inl hl)
      · exact Or.inl (Or.inl (Or.inr hm))
      · exact Or.inr (Or.inr hr)
      · exact Or.inl (Or.inr hc)
    · rintro x (⟨y, hy⟩ | ⟨y, hy⟩)
      · apply hfull.subset
        refine ⟨factsV.old_subset x.property, ?_⟩
        change f x ∈ τ '' tube
        rw [← factsV.keep x, ← hy]
        have hk := P.sourceV.keepL y
        change P.gV (P.sourceV.jL y) = _ at hk
        rw [hk]
        exact hreplace true false y
      · apply hfull.subset
        refine ⟨factsV.old_subset x.property, ?_⟩
        change f x ∈ τ '' tube
        rw [← factsV.keep x, ← hy]
        have hk := P.sourceV.keepR y
        change P.gV (P.sourceV.jR y) = _ at hk
        rw [hk]
        exact hreplace true true y
    · exact havoid

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
