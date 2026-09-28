import PoincareConjecture.Proofs.M76.Mathlib.FineSimplicialSubdivision



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.CollarMesh

theorem exists_subdivision_cofaces_over_disjoint_supports
    {D X κ : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [TopologicalSpace X] [Finite κ]
    (K : SimplicialComplex ℝ D) (hK : K.faces.Finite)
    {g : D → X} (hg : ContinuousOn g K.space)
    (A U : κ → Set X) (hA : ∀ i, IsClosed (A i))
    (hU : ∀ i, IsOpen (U i)) (hAU : ∀ i, A i ⊆ U i)
    (hdis : Pairwise (fun i j => Disjoint (U i) (U j))) :
    ∃ J : SimplicialComplex ℝ D, J.faces.Finite ∧ J.IsSubdivision K ∧
      ∀ i s, s ∈ J.faces → (g '' convexHull ℝ (s : Set D) ∩ A i).Nonempty →
        ∀ t ∈ J.faces, s ⊆ t → MapsTo g (convexHull ℝ (t : Set D)) (U i) := by
  classical
  let W : Option κ → Set K.space
    | none => (fun x => g x) ⁻¹' (⋃ i, A i)ᶜ
    | some i => (fun x => g x) ⁻¹' U i
  have hW : ∀ i, IsOpen (W i) := by
    intro i
    cases i with
    | none => exact (isClosed_iUnion_of_finite hA).isOpen_compl.preimage hg.domRestrict
    | some i => exact (hU i).preimage hg.domRestrict
  have hcover : ∀ x : K.space, ∃ i, x ∈ W i := by
    intro x
    by_cases hx : g x ∈ ⋃ i, A i
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact ⟨some i, hAU i hi⟩
    · exact ⟨none, hx⟩
  obtain ⟨J, hJ, hJK, hstars⟩ := K.exists_finite_subdivision_stars hK W hW hcover
  refine ⟨J, hJ, hJK, ?_⟩
  intro i s hs hmeet
  obtain ⟨y, ⟨x, hxs, rfl⟩, hxA⟩ := hmeet
  obtain ⟨p, hp⟩ := J.nonempty_of_mem_faces hs
  have hcoface (t : Finset D) (ht : t ∈ J.faces) (hst : s ⊆ t) :
      convexHull ℝ (t : Set D) ⊆ (J.closedFaceStar {p}).space := by
    apply (J.closedFaceStar {p}).convexHull_subset_space
    refine ⟨ht, ?_⟩
    simpa only [Finset.union_eq_right.mpr (Finset.singleton_subset_iff.mpr (hst hp))] using ht
  obtain ⟨j, hj⟩ := hstars p (J.face_subset_vertices hs hp)
  have hxK : x ∈ K.space := hJK.space_eq.subset (J.convexHull_subset_space hs hxs)
  have hxW := hj ⟨x, hxK⟩ (hcoface s hs (Subset.refl _) hxs)
  cases j with
  | none => exact False.elim (hxW (mem_iUnion.mpr ⟨i, hxA⟩))
  | some j =>
    have hji : j = i := by
      by_contra hn
      exact disjoint_left.mp (hdis hn) hxW (hAU i hxA)
    subst j
    intro t ht hst z hz
    have hzK : z ∈ K.space := hJK.space_eq.subset (J.convexHull_subset_space ht hz)
    exact hj ⟨z, hzK⟩ (hcoface t ht hst hz)

end PoincareConjecture.M76.CollarMesh
