import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.ConvexCoverSurfaceCount
import PoincareConjecture.Proofs.M76.Mathlib.FiniteFaceSpan
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem space_singleton_finiteFaceSpan (K : SimplicialComplex ℝ E) (s : K.faces) :
    (K.finiteFaceSpan {s}).space = convexHull ℝ (s.val : Set E) := by
  classical
  simp [finiteFaceSpan, space_ofGenerators]

theorem surfaceEulerCount_eq_of_retained_faces
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hL : L.faces.Finite)
    (hdim : ∀ s ∈ K.faces, s.card ≤ 3) (hspace : K.space = L.space)
    (hretain : ∀ s ∈ K.faces, ∃ D : SimplicialComplex ℝ E,
      D ≤ L ∧ D.space = convexHull ℝ (s : Set E)) :
    K.surfaceEulerCount = L.surfaceEulerCount := by
  classical
  let : Fintype K.faces := hK.fintype
  let C (s : K.faces) := K.finiteFaceSpan {s}
  choose D hDL hDs using fun s : K.faces => hretain s.val s.property
  have hCs (s : K.faces) : (C s).space = convexHull ℝ (s.val : Set E) :=
    K.space_singleton_finiteFaceSpan s
  have hCD (s : K.faces) : (C s).space = (D s).space := (hCs s).trans (hDs s).symm
  have hcover : K.space = ⋃ s : K.faces, (C s).space := by
    ext x
    simp only [mem_space_iff, mem_iUnion, hCs]
    exact ⟨fun ⟨s, hs, hx⟩ => ⟨⟨s, hs⟩, hx⟩, fun ⟨s, hx⟩ => ⟨s.val, s.property, hx⟩⟩
  have hCcover : K.space = ⋃ s ∈ (Finset.univ : Finset K.faces), (C s).space := by
    simpa using hcover
  have hDcover : L.space = ⋃ s ∈ (Finset.univ : Finset K.faces), (D s).space := by
    rw [← hspace, hCcover]
    simp only [hCD]
  let P (s : K.faces) := affineSpan ℝ (s.val : Set E)
  have hP (s : K.faces) : Module.finrank ℝ (P s).direction ≤ 2 := by
    let : Nonempty s.val := (K.nonempty_of_mem_faces s.property).to_subtype
    have h := finrank_vectorSpan_range_add_one_le ℝ ((↑) : s.val → E)
    have hrange : range ((↑) : s.val → E) = (s.val : Set E) := by ext; simp
    rw [hrange, Fintype.card_coe] at h
    change Module.finrank ℝ (affineSpan ℝ (s.val : Set E)).direction ≤ 2
    rw [direction_affineSpan]
    have hc := hdim s.val s.property
    omega
  exact surfaceEulerCount_eq_of_common_convex_cover K L hK hL C D
    (fun s => K.finiteFaceSpan_le {s}) hDL hCD
    (fun s => hCs s ▸ convex_convexHull ℝ _) P
    (fun s => by rw [hCs]; exact convexHull_subset_affineSpan _) hP Finset.univ
    (K.faces_eq_biUnion_of_subcomplex_cover C (fun s => K.finiteFaceSpan_le {s}) _ hCcover)
    (L.faces_eq_biUnion_of_subcomplex_cover D hDL _ hDcover)

theorem surfaceEulerCount_eq_of_space_eq
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hL : L.faces.Finite)
    (hdimK : ∀ s ∈ K.faces, s.card ≤ 3) (hdimL : ∀ s ∈ L.faces, s.card ≤ 3)
    (hspace : K.space = L.space) : K.surfaceEulerCount = L.surfaceEulerCount := by
  classical
  let : Finite K.faces := hK.to_subtype
  let : Finite L.faces := hL.to_subtype
  let J : K.faces ⊕ L.faces → SimplicialComplex ℝ E :=
    Sum.elim (fun s => K.finiteFaceSpan {s}) (fun s => L.finiteFaceSpan {s})
  have hJ : ∀ i, (J i).faces.Finite := by
    intro i
    cases i with
    | inl s => exact K.finiteFaceSpan_finite {s}
    | inr s => exact L.finiteFaceSpan_finite {s}
  have hJK : ∀ i, (J i).space ⊆ K.space := by
    intro i
    cases i with
    | inl s =>
      rw [show J (.inl s) = K.finiteFaceSpan {s} from rfl, K.space_singleton_finiteFaceSpan]
      exact K.convexHull_subset_space s.property
    | inr s =>
      rw [show J (.inr s) = L.finiteFaceSpan {s} from rfl, L.space_singleton_finiteFaceSpan, hspace]
      exact L.convexHull_subset_space s.property
  obtain ⟨R, D, hR, hRK, hD⟩ := K.exists_subdivision_with_finite_polyhedra hK J hJ hJK
  have hKRcount : K.surfaceEulerCount = R.surfaceEulerCount :=
    K.surfaceEulerCount_eq_of_retained_faces R hK hR hdimK hRK.space_eq.symm (by
      intro s hs
      exact ⟨D (.inl ⟨s, hs⟩), (hD _).1,
        (hD _).2.trans (K.space_singleton_finiteFaceSpan ⟨s, hs⟩)⟩)
  have hLRcount : L.surfaceEulerCount = R.surfaceEulerCount :=
    L.surfaceEulerCount_eq_of_retained_faces R hL hR hdimL
      (hspace.symm.trans hRK.space_eq.symm) (by
        intro s hs
        exact ⟨D (.inr ⟨s, hs⟩), (hD _).1,
          (hD _).2.trans (L.space_singleton_finiteFaceSpan ⟨s, hs⟩)⟩)
  exact hKRcount.trans hLRcount.symm

end Geometry.SimplicialComplex
