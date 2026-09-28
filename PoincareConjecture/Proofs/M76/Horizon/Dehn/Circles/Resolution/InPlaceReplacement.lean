import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.TargetMapPasting
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.OrdinaryModel











set_option autoImplicit false

open Set Metric Geometry
open PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem OrdinaryDoubleCurveModel.exists_in_place_circle_resolution
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    (old : OrdinaryDoubleCurveModel e f R)
    (hf : PolyhedralPLInCharts e f D2) (he : PLDomain e R)
    (hin : MapsTo f D2 R)
    (hfront : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    (K A : SimplicialComplex ℝ V2) (hK : K.faces.Finite) (hA : A.faces.Finite)
    (hcover : K.space ∪ A.space = D2) (hAQ : Disjoint A.space Q2)
    (a : V2 → X) (ha : PolyhedralPLInCharts e a A.space)
    (haR : MapsTo a A.space (interior R)) (haj : InjOn a A.space)
    (hagree : ∀ x ∈ K.space, x ∈ A.space → f x = a x)
    (hcross : ∀ x ∈ A.space, ∀ y ∈ K.space, a x = f y → x = y)
    (i : old.Index) (htrace : A.space ∩ doubleLocusOn f D2 = old.pieces i)
    (hremoved : Disjoint K.space (old.pieces i)) :
    ∃ g : V2 → X, PolyhedralPLInCharts e g D2 ∧
      EqOn g f K.space ∧ EqOn g a A.space ∧ MapsTo g D2 R ∧ EqOn g f Q2 ∧
      (∀ x ∈ D2, g x ∈ frontier R ↔ x ∈ Q2) ∧
      g '' D2 = f '' K.space ∪ a '' A.space ∧
      doubleBoundaryComponentCount g D2 Q2 ≤ doubleBoundaryComponentCount f D2 Q2 ∧
      doubleInteriorComponentCount g D2 Q2 < doubleInteriorComponentCount f D2 Q2 ∧
      Nonempty (OrdinaryDoubleCurveModel e g R) := by
  have hKD : K.space ⊆ D2 := fun x hx ↦ hcover.subset (Or.inl hx)
  have hAD : A.space ⊆ D2 := fun x hx ↦ hcover.subset (Or.inr hx)
  have hwhole : ∀ j, old.pieces j ⊆ K.space ∨ Disjoint (old.pieces j) K.space := by
    intro j
    by_cases hji : j = i
    · subst j
      exact Or.inr hremoved.symm
    · apply Or.inl
      intro x hx
      have hxdouble : x ∈ doubleLocusOn f D2 :=
        old.cover.subset (mem_iUnion.mpr ⟨j, hx⟩)
      apply (hcover.symm.subset hxdouble.1).resolve_right
      intro hxA
      exact disjoint_left.mp (old.disjoint hji) hx (htrace.subset ⟨hxA, hxdouble⟩)
  have havoid : Disjoint (K.space ∩ doubleLocusOn f D2) A.space := by
    apply disjoint_left.mpr
    intro x hx hxA
    exact disjoint_left.mp hremoved hx.1 (htrace.subset ⟨hxA, hx.2⟩)
  have hiQ : Disjoint (old.pieces i) Q2 :=
    hAQ.mono_left (htrace.symm.subset.trans inter_subset_left)
  have hiK : ¬ old.pieces i ⊆ K.space := by
    intro hi
    obtain ⟨x, hx⟩ := (old.connected i).nonempty
    exact disjoint_left.mp hremoved (hi hx) hx
  obtain ⟨g, hg, hgK, hgA⟩ := _root_.Dehn.exists_circle_attachment_map_union
    he.compatible K A hK hA (hf.restrict_finite K hK hKD) ha hagree
  have hgD : PolyhedralPLInCharts e g D2 := hcover ▸ hg
  let j : K.space → V2 := Subtype.val
  have hjs : range j = K.space := Subtype.range_val
  have hjcover : range j ∪ A.space = D2 := by rw [hjs, hcover]
  have hsingle : ∀ z ∈ A.space, ∀ w ∈ D2, g w = g z → w = z := by
    intro z hz w hw hwz
    rcases hcover.symm.subset hw with hwK | hwA
    · rw [hgK hwK, hgA hz] at hwz
      exact (hcross z hz w hwK hwz.symm).symm
    · rw [hgA hwA, hgA hz] at hwz
      exact haj hwA hz hwz
  have facts : RetainedSquareMapFacts f g K.space j := {
    old_subset := hKD
    injective := Subtype.val_injective
    continuous := continuous_subtype_val
    mapsTo := fun x ↦ hKD x.property
    keep := fun x ↦ hgK x.property
    boundary := fun _ ↦ Iff.rfl
    double_relation := retained_double_relation_eq j Subtype.val_injective
      hjcover (fun x ↦ hgK x.property) hsingle
    double_locus := retained_double_locus_eq j Subtype.val_injective
      hjcover (fun x ↦ hgK x.property) hsingle }
  have hid : FinitePiecewiseAffineOn (id : V2 → V2) K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V2)⟩
  have hAcompact : IsCompact A.space :=
    (show FinitePiecewiseAffineOn (id : V2 → V2) A.space from
      ⟨A, hA, rfl, A.affineOnFaces_affine (ContinuousAffineMap.id ℝ V2)⟩).isCompact
  obtain ⟨H⟩ := facts.nonempty_open_source_restriction hid.isCompact
    hAcompact.isClosed hAcompact.isClosed hcover.symm.subset hjcover.symm.subset
    (fun _ hx ↦ hx) (fun x hx ↦ disjoint_left.mp havoid ⟨x.property, hx⟩)
  obtain ⟨model, hboundary, hinterior⟩ := facts.ordinary_circle_resolution old
    hf.continuousOn hgD.continuousOn ⟨id, hid, fun _ ↦ rfl⟩ H hwhole i hiQ hiK
  have hrim : EqOn g f Q2 := by
    intro x hx
    exact hgK ((hcover.symm.subset (sphere_subset_closedBall hx)).resolve_right
      (fun hxa ↦ disjoint_left.mp hAQ hxa hx))
  refine ⟨g, hgD, hgK, hgA, ?_, hrim, ?_, ?_, hboundary, hinterior, model⟩
  · intro x hx
    rcases hcover.symm.subset hx with hxK | hxA
    · rw [hgK hxK]
      exact hin hx
    · rw [hgA hxA]
      exact interior_subset (haR hxA)
  · intro x hx
    rcases hcover.symm.subset hx with hxK | hxA
    · rw [hgK hxK]
      exact hfront x hx
    · rw [hgA hxA]
      exact iff_of_false
        (fun h ↦ disjoint_left.mp disjoint_interior_frontier (haR hxA) h)
        (fun h ↦ disjoint_left.mp hAQ hxA h)
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hcover.symm.subset hx with hxK | hxA
      · exact Or.inl ⟨x, hxK, (hgK hxK).symm⟩
      · exact Or.inr ⟨x, hxA, (hgA hxA).symm⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact ⟨x, hKD hx, hgK hx⟩
      · exact ⟨x, hAD hx, hgA hx⟩

end PoincareConjecture.M76.Dehn
