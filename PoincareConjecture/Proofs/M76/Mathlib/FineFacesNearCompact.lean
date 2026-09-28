import PoincareConjecture.Proofs.M76.Mathlib.FineSimplicialSubdivision













set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]






theorem exists_subdivision_faces_near_compact
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {A : Set E} (hA : IsCompact A) (hAK : A ⊆ K.space)
    {O : Set K.space} (hO : IsOpen O)
    (hAO : ∀ x : K.space, (x : E) ∈ A → x ∈ O) :
    ∃ (R : SimplicialComplex ℝ E) (P : Set E),
      R.faces.Finite ∧ R.IsSubdivision K ∧ IsCompact P ∧ A ⊆ P ∧
      P ⊆ Subtype.val '' O ∧
      ∀ s ∈ R.faces, (convexHull ℝ (s : Set E) ∩ A).Nonempty →
        convexHull ℝ (s : Set E) ⊆ P := by
  classical
  let U : Bool → Set K.space := fun b => if b then O else Subtype.val ⁻¹' Aᶜ
  have hU (b : Bool) : IsOpen (U b) := by
    cases b
    · exact hA.isClosed.isOpen_compl.preimage continuous_subtype_val
    · exact hO
  have hcover (x : K.space) : ∃ b, x ∈ U b := by
    by_cases hx : (x : E) ∈ A
    · exact ⟨true, hAO x hx⟩
    · exact ⟨false, hx⟩
  obtain ⟨R, hR, hRK, hstars⟩ := K.exists_finite_subdivision_stars hK U hU hcover
  have hface (s : Finset E) (hs : s ∈ R.faces)
      (hmeet : (convexHull ℝ (s : Set E) ∩ A).Nonempty) :
      convexHull ℝ (s : Set E) ⊆ Subtype.val '' O := by
    obtain ⟨x, hxs, hxA⟩ := hmeet
    obtain ⟨p, hps⟩ := R.nonempty_of_mem_faces hs
    have hp : {p} ∈ R.faces :=
      R.down_closed hs (Finset.singleton_subset_iff.mpr hps) (Finset.singleton_nonempty p)
    have hpss : {p} ⊆ s := Finset.singleton_subset_iff.mpr hps
    have hsstar : s ∈ (R.closedFaceStar {p}).faces :=
      ⟨hs, by simpa only [Finset.union_eq_right.mpr hpss] using hs⟩
    have hstar : convexHull ℝ (s : Set E) ⊆ (R.closedFaceStar {p}).space :=
      (R.closedFaceStar {p}).convexHull_subset_space hsstar
    obtain ⟨b, hb⟩ := hstars p hp
    have hbtrue : b = true := by
      cases b
      · exact False.elim ((hb ⟨x, hAK hxA⟩ (hstar hxs)) hxA)
      · rfl
    intro y hys
    have hyK : y ∈ K.space := hRK.space_eq ▸ R.convexHull_subset_space hs hys
    refine ⟨⟨y, hyK⟩, ?_, rfl⟩
    simpa only [hbtrue, U, if_true] using hb ⟨y, hyK⟩ (hstar hys)
  let F : Set (Finset E) :=
    {s | s ∈ R.faces ∧ (convexHull ℝ (s : Set E) ∩ A).Nonempty}
  have hF : F.Finite := hR.subset (fun _ hs => hs.1)
  let P : Set E := ⋃ s ∈ F, convexHull ℝ (s : Set E)
  refine ⟨R, P, hR, hRK, hF.isCompact_biUnion
    (fun s _ => s.finite_toSet.isCompact_convexHull ℝ), ?_, ?_, ?_⟩
  · intro x hx
    have hxR : x ∈ R.space := hRK.space_eq.symm ▸ hAK hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hxR
    exact mem_iUnion₂.mpr ⟨s, ⟨hs, x, hxs, hx⟩, hxs⟩
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    exact hface s hs.1 hs.2 hxs
  · intro s hs hmeet x hx
    exact mem_iUnion₂.mpr ⟨s, ⟨hs, hmeet⟩, hx⟩

end Geometry.SimplicialComplex
