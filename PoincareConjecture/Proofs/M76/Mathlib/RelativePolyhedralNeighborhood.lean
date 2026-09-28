import PoincareConjecture.Proofs.M76.Mathlib.FineSimplicialSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.FiniteFaceStarNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLGluing
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_relative_polyhedral_neighborhood
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (x : K.space) {O : Set K.space} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ (J : SimplicialComplex ℝ E) (V : Set K.space),
      J.faces.Finite ∧ J.space ⊆ K.space ∧ IsOpen V ∧ x ∈ V ∧
      Subtype.val '' V ⊆ J.space ∧
      (Subtype.val : K.space → E) ⁻¹' J.space ⊆ O := by
  classical
  let U : Bool → Set K.space := fun b => if b then O else {x}ᶜ
  have hU (b : Bool) : IsOpen (U b) := by
    cases b
    · exact isClosed_singleton.isOpen_compl
    · exact hO
  have hcover (y : K.space) : ∃ b, y ∈ U b := by
    by_cases hy : y = x
    · refine ⟨true, ?_⟩
      change y ∈ O
      rwa [hy]
    · exact ⟨false, hy⟩
  obtain ⟨L, hL, hLK, hstars⟩ := K.exists_finite_subdivision_stars hK U hU hcover
  let H : L.space ≃ₜ K.space := Homeomorph.setCongr hLK.space_eq
  let xL : L.space := H.symm x
  obtain ⟨s, hs, hxs, V, hV, hxV, hVS⟩ :=
    L.exists_faceStar_neighborhood_of_finite hL xL
  obtain ⟨p, hps⟩ := L.nonempty_of_mem_faces hs
  have hp : {p} ∈ L.faces :=
    L.down_closed hs (Finset.singleton_subset_iff.mpr hps) (Finset.singleton_nonempty p)
  have hSP : (L.closedFaceStar s).space ⊆ (L.closedFaceStar {p}).space :=
    space_subset_of_le (L.closedFaceStar_antitone (Finset.singleton_subset_iff.mpr hps))
  have hxS : (x : E) ∈ (L.closedFaceStar s).space :=
    hVS (mem_image_of_mem Subtype.val hxV)
  obtain ⟨b, hb⟩ := hstars p hp
  have hbtrue : b = true := by
    cases b
    · exact False.elim ((hb x (hSP hxS)) (mem_singleton x))
    · rfl
  have hSO : (Subtype.val : K.space → E) ⁻¹' (L.closedFaceStar s).space ⊆ O := by
    intro y hy
    have h := hb y (hSP hy)
    simpa only [hbtrue, U, if_true] using h
  refine ⟨L.closedFaceStar s, H '' V, finite_closedFaceStar_faces hL s,
    ?_, H.isOpenMap V hV, ⟨xL, hxV, H.apply_symm_apply x⟩, ?_, hSO⟩
  · intro y hy
    exact hLK.space_eq.subset (space_subset_of_le (L.closedFaceStar_le s) hy)
  · rintro _ ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact hVS (mem_image_of_mem Subtype.val hz)

theorem finitePiecewiseAffineOn_of_relative_local
    [FiniteDimensional ℝ E] (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → F}
    (hf : ∀ x : K.space, ∃ (J : SimplicialComplex ℝ E) (V : Set K.space),
      J.faces.Finite ∧ IsOpen V ∧ x ∈ V ∧
      Subtype.val '' V ⊆ J.space ∧ J.AffineOnFaces f) :
    FinitePiecewiseAffineOn f K.space := by
  classical
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp
    (K.isCompact_space_of_finite hK)
  choose J V hJ hV hxV hVJ hfJ using hf
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hV
    (fun x _ => mem_iUnion.mpr ⟨x, hxV x⟩)
  apply Geometry.finitePiecewiseAffineOn_of_finite_cover K hK
    (fun x : t => J x) (fun x => hJ x) (fun x => hfJ x)
  intro x hx
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht (mem_univ (⟨x, hx⟩ : K.space)))
  exact mem_iUnion.mpr ⟨⟨y, hyt⟩, hVJ y (mem_image_of_mem Subtype.val hxy)⟩

end Geometry.SimplicialComplex
