import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.FineSimplicialSubdivision
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.FiniteCarrierFaceInteriors
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coverings.ClosedStarProjectionCoverage

/-! # Simultaneous coface neighborhoods along a closed contact set -/

set_option autoImplicit false
open Set Geometry

namespace PoincareMT.M76

theorem subdivision_preserves_contact_coface_neighborhoods
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K J : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hJK : J.IsSubdivision K)
    (C : Set E) (U : I → Set E)
    (hcofaces : ∀ s ∈ K.faces, (convexHull ℝ (s : Set E) ∩ C).Nonempty →
      ∃ i, ∀ t ∈ K.faces, s ⊆ t → convexHull ℝ (t : Set E) ⊆ U i) :
    ∀ s ∈ J.faces, (convexHull ℝ (s : Set E) ∩ C).Nonempty →
      ∃ i, ∀ t ∈ J.faces, s ⊆ t → convexHull ℝ (t : Set E) ⊆ U i := by
  classical
  intro s hs hmeet
  obtain ⟨x, hxs, hxC⟩ := hmeet
  have hxK : x ∈ K.space := hJK.space_eq.subset (J.convexHull_subset_space hs hxs)
  obtain ⟨a, ha, hxa⟩ := K.exists_face_intrinsicInterior_of_finite hK hxK
  obtain ⟨i, hi⟩ := hcofaces a ha ⟨x, intrinsicInterior_subset hxa, hxC⟩
  refine ⟨i, ?_⟩
  intro t ht hst
  obtain ⟨b, hb, htb⟩ := hJK.face_subset t ht
  have hxb : x ∈ convexHull ℝ (b : Set E) := htb (convexHull_mono hst hxs)
  exact htb.trans (hi b hb (K.subset_of_mem_intrinsicInterior_face ha hb hxa hxb))

theorem exists_subdivision_cofaces_near_closed_contacts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {C : Set E} (hC : IsClosed C) (U : C → Set E)
    (hU : ∀ x, IsOpen (U x)) (hxU : ∀ x : C, (x : E) ∈ U x) :
    ∃ J : SimplicialComplex ℝ E, J.faces.Finite ∧ J.IsSubdivision K ∧
      ∀ s ∈ J.faces, (convexHull ℝ (s : Set E) ∩ C).Nonempty →
        ∃ x : C, ∀ t ∈ J.faces, s ⊆ t → convexHull ℝ (t : Set E) ⊆ U x := by
  classical
  let W : Option C → Set K.space
    | none => Subtype.val ⁻¹' Cᶜ
    | some x => Subtype.val ⁻¹' U x
  have hW : ∀ i, IsOpen (W i) := by
    intro i
    cases i with
    | none => exact hC.isOpen_compl.preimage continuous_subtype_val
    | some x => exact (hU x).preimage continuous_subtype_val
  have hcover : ∀ x : K.space, ∃ i, x ∈ W i := by
    intro x
    by_cases hx : (x : E) ∈ C
    · exact ⟨some ⟨x, hx⟩, hxU ⟨x, hx⟩⟩
    · exact ⟨none, hx⟩
  obtain ⟨J, hJ, hJK, hstars⟩ := K.exists_finite_subdivision_stars hK W hW hcover
  refine ⟨J, hJ, hJK, ?_⟩
  intro s hs hmeet
  obtain ⟨p, hp⟩ := J.nonempty_of_mem_faces hs
  have hpJ : {p} ∈ J.faces := J.face_subset_vertices hs hp
  have hcoface (t : Finset E) (ht : t ∈ J.faces) (hst : s ⊆ t) :
      convexHull ℝ (t : Set E) ⊆ (J.closedFaceStar {p}).space := by
    apply (J.closedFaceStar {p}).convexHull_subset_space
    refine ⟨ht, ?_⟩
    simpa only [Finset.union_eq_right.mpr (Finset.singleton_subset_iff.mpr (hst hp))] using ht
  obtain ⟨i, hi⟩ := hstars p hpJ
  cases i with
  | none =>
    obtain ⟨z, hzs, hzC⟩ := hmeet
    have hzK : z ∈ K.space := hJK.space_eq.subset (J.convexHull_subset_space hs hzs)
    exact False.elim ((hi ⟨z, hzK⟩ (hcoface s hs (Subset.refl _) hzs)) hzC)
  | some x =>
    refine ⟨x, ?_⟩
    intro t ht hst z hz
    have hzK : z ∈ K.space := hJK.space_eq.subset (J.convexHull_subset_space ht hz)
    exact hi ⟨z, hzK⟩ (hcoface t ht hst hz)

end PoincareMT.M76
