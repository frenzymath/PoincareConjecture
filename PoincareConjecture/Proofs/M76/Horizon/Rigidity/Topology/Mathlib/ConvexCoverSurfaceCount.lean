import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SurfaceCountInclusionExclusion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.LowDimensionalConvexCount
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.RefinementEdgeStars
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCarrierFaceInteriors

set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*}

omit [FiniteDimensional ℝ E] in
theorem space_finset_inf'_of_common_subcomplex
    (R : SimplicialComplex ℝ E) (hR : R.faces.Finite)
    (C : ι → SimplicialComplex ℝ E) (hC : ∀ i, C i ≤ R)
    (S : Finset ι) (hne : S.Nonempty) :
    (S.inf' hne C).space = ⋂ i ∈ S, (C i).space := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    simp only [mem_iInter]
    intro i hi
    exact (C i).convexHull_subset_space (Finset.inf'_le C hi hs) hxs
  · intro hx
    have hall : ∀ i ∈ S, x ∈ (C i).space := by simpa using hx
    let i := hne.choose
    have hi : i ∈ S := hne.choose_spec
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp (hall i hi)
    have hxR : x ∈ R.space := R.convexHull_subset_space (hC i ht) hxt
    obtain ⟨s, hs, hxs⟩ := R.exists_face_intrinsicInterior_of_finite hR hxR
    refine mem_space_iff.mpr ⟨s, ?_, intrinsicInterior_subset hxs⟩
    rw [faces_finset_inf']
    exact mem_iInter₂.mpr (fun i hi =>
      R.face_mem_subcomplex_of_intrinsicInterior (C i) (hC i) hs hxs (hall i hi))

omit [FiniteDimensional ℝ E] in
theorem surfaceEulerCount_eq_zero_of_space_empty
    (K : SimplicialComplex ℝ E) (he : K.space = ∅) : K.surfaceEulerCount = 0 := by
  have hfaces : K.faces = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s hs
    obtain ⟨p, hp⟩ := K.nonempty_of_mem_faces hs
    have hx := K.convexHull_subset_space hs (subset_convexHull ℝ _ hp)
    rw [he] at hx
    exact hx
  have hcard (n : ℕ) : Nat.card (K.FaceOfCard n) = 0 := by
    have hempty : IsEmpty (K.FaceOfCard n) := ⟨fun s => by simpa [hfaces] using s.property.1⟩
    exact Nat.card_of_isEmpty
  simp only [surfaceEulerCount, hcard, Nat.cast_zero, sub_self, add_zero]

theorem faces_eq_biUnion_of_subcomplex_cover
    (K : SimplicialComplex ℝ E) (C : ι → SimplicialComplex ℝ E)
    (hCK : ∀ i, C i ≤ K) (S : Finset ι)
    (hcover : K.space = ⋃ i ∈ S, (C i).space) :
    K.faces = ⋃ i ∈ S, (C i).faces := by
  ext s
  constructor
  · intro hs
    have hne : (convexHull ℝ (s : Set E)).Nonempty := by
      obtain ⟨p, hp⟩ := K.nonempty_of_mem_faces hs
      exact ⟨p, subset_convexHull ℝ _ hp⟩
    obtain ⟨x, hx⟩ := hne.intrinsicInterior (convex_convexHull ℝ _)
    have hxK := K.convexHull_subset_space hs (intrinsicInterior_subset hx)
    rw [hcover] at hxK
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxK
    exact mem_iUnion₂.mpr ⟨i, hi,
      K.face_mem_subcomplex_of_intrinsicInterior (C i) (hCK i) hs hx hxi⟩
  · intro hs
    obtain ⟨i, _, hi⟩ := mem_iUnion₂.mp hs
    exact hCK i hi

theorem surfaceEulerCount_eq_of_common_convex_cover
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hL : L.faces.Finite)
    (C D : ι → SimplicialComplex ℝ E)
    (hCK : ∀ i, C i ≤ K) (hDL : ∀ i, D i ≤ L)
    (hCD : ∀ i, (C i).space = (D i).space)
    (hc : ∀ i, Convex ℝ (C i).space)
    (P : ι → AffineSubspace ℝ E)
    (hCP : ∀ i, (C i).space ⊆ P i)
    (hdim : ∀ i, Module.finrank ℝ (P i).direction ≤ 2)
    (S : Finset ι)
    (hcoverK : K.faces = ⋃ i ∈ S, (C i).faces)
    (hcoverL : L.faces = ⋃ i ∈ S, (D i).faces) :
    K.surfaceEulerCount = L.surfaceEulerCount := by
  classical
  let hCf := fun i => hK.subset (hCK i)
  let hDf := fun i => hL.subset (hDL i)
  rw [surfaceEulerCount_inclusion_exclusion C hCf S K hcoverK,
    surfaceEulerCount_inclusion_exclusion D hDf S L hcoverL]
  apply Finset.sum_congr rfl
  intro T _
  congr 1
  let hT := (Finset.mem_filter.mp T.property).2
  let A := T.val.inf' hT C
  let B := T.val.inf' hT D
  have hA := K.space_finset_inf'_of_common_subcomplex hK C hCK T.val hT
  have hB := L.space_finset_inf'_of_common_subcomplex hL D hDL T.val hT
  have hAB : A.space = B.space := by rw [hA, hB]; simp only [hCD]
  obtain ⟨i, hi⟩ := hT
  have hAc : Convex ℝ A.space := by
    rw [hA]
    exact convex_iInter (fun i => convex_iInter (fun _ => hc i))
  have hAP : A.space ⊆ P i := by
    rw [hA]
    exact fun x hx => hCP i (mem_iInter₂.mp hx i hi)
  by_cases hne : A.space.Nonempty
  · have hAf : A.faces.Finite := (hCf i).subset (Finset.inf'_le C hi)
    have hBf : B.faces.Finite := (hDf i).subset (Finset.inf'_le D hi)
    rw [A.surfaceEulerCount_eq_one_of_convex_low_dimension hAf hAc hne (P i) hAP (hdim i),
      B.surfaceEulerCount_eq_one_of_convex_low_dimension hBf (hAB ▸ hAc)
        (hAB ▸ hne) (P i) (hAB ▸ hAP) (hdim i)]
  · have hAe := Set.not_nonempty_iff_eq_empty.mp hne
    rw [A.surfaceEulerCount_eq_zero_of_space_empty hAe,
      B.surfaceEulerCount_eq_zero_of_space_empty (hAB.symm.trans hAe)]

end Geometry.SimplicialComplex
