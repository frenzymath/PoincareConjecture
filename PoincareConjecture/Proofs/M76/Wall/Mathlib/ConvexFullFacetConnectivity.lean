import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionConvexTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIntrinsicDensity
import PoincareConjecture.Proofs.M76.Mathlib.AffineSubspaceAvoidance
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkDimension
import PoincareConjecture.Proofs.M76.Mathlib.FullSimplexBasis
import PoincareConjecture.Proofs.M76.Mathlib.SimplexRelativeInteriorCoordinates
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev FullFaceIn (K : SimplicialComplex ℝ E) (U : Set E) :=
  {t : Finset E // t ∈ K.faces ∧ t.card = Module.finrank ℝ E + 1 ∧
    (convexHull ℝ (t : Set E) ∩ U).Nonempty}

def fullFacetGraph (K : SimplicialComplex ℝ E) (U : Set E) :
    SimpleGraph (K.FullFaceIn U) where
  Adj t u := t ≠ u ∧ ∃ s ∈ K.faces, s.card = Module.finrank ℝ E ∧
    s ⊆ t.val ∧ s ⊆ u.val ∧ (convexHull ℝ (s : Set E) ∩ U).Nonempty
  symm := ⟨by
    rintro t u ⟨hne, s, hs, hc, hst, hsu, hmeet⟩
    exact ⟨Ne.symm hne, s, hs, hc, hsu, hst, hmeet⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable [FiniteDimensional ℝ E]

private theorem full_face_meets_avoiding_open
    {K : SimplicialComplex ℝ E} {U : Set E} (hU : IsOpen U)
    (t : K.FullFaceIn U) {ι : Type*} [Finite ι]
    (A : ι → AffineSubspace ℝ E) (hA : ∀ i, A i ≠ ⊤) :
    ((U \ ⋃ i, (A i : Set E)) ∩ convexHull ℝ (t.val : Set E)).Nonempty := by
  obtain ⟨x, hx, hxU⟩ :=
    (convex_convexHull ℝ (t.val : Set E)).intrinsicInterior_inter_open_nonempty
      hU t.property.2.2
  let b := (K.indep t.property.1).affineBasisOfCard t.property.2.1
  have hxint : x ∈ interior (convexHull ℝ (t.val : Set E)) := by
    have h : x ∈ interior (convexHull ℝ (range b)) :=
      b.mem_interior_convexHull_of_mem_intrinsicInterior (by simpa [b] using hx)
    simpa [b] using h
  obtain ⟨y, hy, hyA⟩ := (AffineSubspace.dense_compl_iUnion A hA).inter_open_nonempty
    (U ∩ interior (convexHull ℝ (t.val : Set E))) (hU.inter isOpen_interior)
    ⟨x, hxU, hxint⟩
  exact ⟨y, ⟨hy.1, hyA⟩, interior_subset hy.2⟩

theorem fullFacetGraph_connected (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {U : Set E} (hU : IsOpen U) (hcv : Convex ℝ U)
    (hne : U.Nonempty) (hUK : U ⊆ K.space) : (K.fullFacetGraph U).Connected := by
  classical
  have hF : {t : Finset E | t ∈ K.faces ∧ t.card = Module.finrank ℝ E + 1 ∧
      (convexHull ℝ (t : Set E) ∩ U).Nonempty}.Finite :=
    hK.subset (fun _ ht => ht.1)
  let : Finite (K.FullFaceIn U) := hF.to_subtype
  let S : Set (Finset E) := {s | s ∈ K.faces ∧ s.card < Module.finrank ℝ E}
  have hS : S.Finite := hK.subset (fun _ hs => hs.1)
  let : Finite S := hS.to_subtype
  let A : S → AffineSubspace ℝ E := fun s => affineSpan ℝ (s.val : Set E)
  have hA : ∀ s, Module.finrank ℝ (A s).direction + 1 < Module.finrank ℝ E := by
    intro s
    have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces s.property.1)
    change Module.finrank ℝ (affineSpan ℝ (s.val : Set E)).direction + 1 < _
    rw [K.finrank_faceDirection_of_card s.property.1
      (show s.val.card = (s.val.card - 1) + 1 by omega)]
    have hlt := s.property.2
    omega
  have hproper : ∀ s, A s ≠ ⊤ := by
    intro s he
    have hd := hA s
    rw [he, AffineSubspace.direction_top, finrank_top] at hd
    omega
  let W := U \ ⋃ s, (A s : Set E)
  have hconn : IsConnected W :=
    (AffineSubspace.isPathConnected_sdiff_iUnion A hA hU hcv hne).isConnected
  have hmeet (t : K.FullFaceIn U) :
      (W ∩ convexHull ℝ (t.val : Set E)).Nonempty :=
    full_face_meets_avoiding_open hU t A hproper
  have hUint : U ⊆ interior K.space := fun x hx =>
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hU.mem_nhds hx) hUK)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨t, ht, htc, hxt⟩ := K.exists_full_face_of_mem_interior hK (hUint hx)
  let : Nonempty (K.FullFaceIn U) := ⟨⟨t, ht, htc, x, hxt, hx⟩⟩
  refine ⟨?_⟩
  intro q r
  let G := K.fullFacetGraph U
  by_contra hnot
  let R : Set (K.FullFaceIn U) := {t | G.Reachable q t}
  let P : Set E := ⋃ t ∈ R, convexHull ℝ (t.val : Set E)
  let Q : Set E := ⋃ t ∈ Rᶜ, convexHull ℝ (t.val : Set E)
  have hP : IsClosed P :=
    ((Set.toFinite R).isCompact_biUnion
      (fun t _ => t.val.finite_toSet.isCompact_convexHull ℝ)).isClosed
  have hQ : IsClosed Q :=
    ((Set.toFinite Rᶜ).isCompact_biUnion
      (fun t _ => t.val.finite_toSet.isCompact_convexHull ℝ)).isClosed
  have hcover : W ⊆ P ∪ Q := by
    intro y hy
    obtain ⟨u, hu, huc, hyu⟩ := K.exists_full_face_of_mem_interior hK (hUint hy.1)
    let v : K.FullFaceIn U := ⟨u, hu, huc, y, hyu, hy.1⟩
    by_cases hv : G.Reachable q v
    · exact Or.inl (mem_iUnion₂.mpr ⟨v, hv, hyu⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨v, hv, hyu⟩)
  have hWP : (W ∩ P).Nonempty := by
    obtain ⟨y, hyW, hyq⟩ := hmeet q
    exact ⟨y, hyW, mem_iUnion₂.mpr ⟨q, SimpleGraph.Reachable.refl q, hyq⟩⟩
  have hWQ : (W ∩ Q).Nonempty := by
    obtain ⟨y, hyW, hyr⟩ := hmeet r
    exact ⟨y, hyW, mem_iUnion₂.mpr ⟨r, hnot, hyr⟩⟩
  obtain ⟨y, hyW, hyP, hyQ⟩ :=
    isPreconnected_closed_iff.mp hconn.isPreconnected P Q hP hQ hcover hWP hWQ
  obtain ⟨t, htR, hyt⟩ := mem_iUnion₂.mp hyP
  obtain ⟨u, huR, hyu⟩ := mem_iUnion₂.mp hyQ
  have htu : t ≠ u := fun he => huR (he ▸ htR)
  let s := t.val ∩ u.val
  have hys : y ∈ convexHull ℝ (s : Set E) := by
    simpa only [s, Finset.coe_inter] using
      K.inter_subset_convexHull t.property.1 u.property.1 ⟨hyt, hyu⟩
  have hsne : s.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.coe_empty, convexHull_empty, mem_empty_iff_false] at hys
  have hst : s ⊆ t.val := Finset.inter_subset_left
  have hsu : s ⊆ u.val := Finset.inter_subset_right
  have hs : s ∈ K.faces := K.down_closed t.property.1 hst hsne
  have hsc : s.card ≤ Module.finrank ℝ E := by
    have hle := Finset.card_le_card hst
    have htcard := t.property.2.1
    have hucard := u.property.2.1
    by_contra hn
    have he : s = t.val := Finset.eq_of_subset_of_card_le hst (by omega)
    have htu' : t.val ⊆ u.val := he ▸ hsu
    exact htu (Subtype.ext (Finset.eq_of_subset_of_card_le htu' (by omega)))
  have hsc' : s.card = Module.finrank ℝ E := by
    by_contra hn
    have hsS : s ∈ S := ⟨hs, by omega⟩
    exact hyW.2 (mem_iUnion.mpr
      ⟨⟨s, hsS⟩, convexHull_subset_affineSpan _ hys⟩)
  have hadj : G.Adj t u := ⟨htu, s, hs, hsc', hst, hsu, y, hys, hyW.1⟩
  exact huR (htR.trans hadj.reachable)

end Geometry.SimplicialComplex
