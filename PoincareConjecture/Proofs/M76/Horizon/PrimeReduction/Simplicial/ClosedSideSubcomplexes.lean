import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PuncturedSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.ConvexIntrinsicInterior

set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_subcomplex_of_closed_side
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L ≤ K)
    {p n : Set E} (hp : IsClosed p) (hn : IsClosed n)
    (hu : p ∪ n = K.space) (hi : p ∩ n = L.space) :
    ∃ P : SimplicialComplex ℝ E, P ≤ K ∧ L ≤ P ∧
      P.faces.Finite ∧ P.space = p := by
  let P : SimplicialComplex ℝ E :=
    { faces := {s | s ∈ K.faces ∧ convexHull ℝ (s : Set E) ⊆ p}
      indep := fun hs => K.indep hs.1
      isRelLowerSet_faces := by
        intro s hs
        refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
        intro t hts ht
        exact ⟨K.down_closed hs.1 hts ht, (convexHull_mono hts).trans hs.2⟩
      inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull hs.1 ht.1 }
  have hPK : P ≤ K := fun _ hs => hs.1
  have hLp : L.space ⊆ p := hi.symm.subset.trans inter_subset_left
  have hLP : L ≤ P := fun _ hs => ⟨hLK hs, (L.convexHull_subset_space hs).trans hLp⟩
  have hPp : P.space ⊆ p := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact hs.2 hxs
  refine ⟨P, hPK, hLP, hK.subset hPK, hPp.antisymm ?_⟩
  intro x hx
  by_cases hxL : x ∈ L.space
  · exact space_subset_of_le hLP hxL
  have hxK : x ∈ K.space := hu.subset (Or.inl hx)
  obtain ⟨s, hs, hxs⟩ := K.exists_face_intrinsicInterior_of_finite hK hxK
  have hnotL : ∀ y ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)), y ∉ L.space := by
    intro y hy hyL
    have hsL := K.face_mem_subcomplex_of_intrinsicInterior L hLK hs hy hyL
    exact hxL (L.convexHull_subset_space hsL (intrinsicInterior_subset hxs))
  have hrel : intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ⊆ p := by
    intro y hy
    by_contra hyp
    have hyn : y ∈ n := (hu.symm.subset
      (K.convexHull_subset_space hs (intrinsicInterior_subset hy))).resolve_left hyp
    obtain ⟨z, hz, hzp, hzn⟩ := isPreconnected_closed_iff.mp
      (convex_convexHull ℝ (s : Set E)).intrinsicInterior.isPreconnected p n hp hn
      (fun z hz => hu.symm.subset (K.convexHull_subset_space hs (intrinsicInterior_subset hz)))
      ⟨x, hxs, hx⟩ ⟨y, hy, hyn⟩
    exact hnotL z hz (hi.subset ⟨hzp, hzn⟩)
  have hface : convexHull ℝ (s : Set E) ⊆ p :=
    (convex_convexHull ℝ (s : Set E)).subset_closure_intrinsicInterior.trans
      (closure_minimal hrel hp)
  exact P.convexHull_subset_space ⟨hs, hface⟩ (intrinsicInterior_subset hxs)

theorem exists_closed_side_subcomplexes
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L ≤ K)
    {p n : Set E} (hp : IsClosed p) (hn : IsClosed n)
    (hu : p ∪ n = K.space) (hi : p ∩ n = L.space) :
    ∃ P M : SimplicialComplex ℝ E,
      P ≤ K ∧ M ≤ K ∧ L ≤ P ∧ L ≤ M ∧ P.faces.Finite ∧ M.faces.Finite ∧
      P.space = p ∧ M.space = n ∧
      (∀ s ∈ K.faces, s ∈ P.faces ∨ s ∈ M.faces) ∧
      P.faces ∩ M.faces = L.faces := by
  obtain ⟨P, hPK, hLP, hP, hPs⟩ := K.exists_subcomplex_of_closed_side L hK hLK hp hn hu hi
  obtain ⟨M, hMK, hLM, hM, hMs⟩ := K.exists_subcomplex_of_closed_side L hK hLK hn hp
    ((union_comm n p).trans hu) ((inter_comm n p).trans hi)
  refine ⟨P, M, hPK, hMK, hLP, hLM, hP, hM, hPs, hMs, ?_, ?_⟩
  · intro s hs
    obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ (s : Set E))
      (Finset.coe_nonempty.mpr (K.nonempty_of_mem_faces hs)).convexHull
    rcases hu.symm.subset (K.convexHull_subset_space hs (intrinsicInterior_subset hx)) with hp | hn
    · exact Or.inl (K.face_mem_subcomplex_of_intrinsicInterior P hPK hs hx (hPs.symm.subset hp))
    · exact Or.inr (K.face_mem_subcomplex_of_intrinsicInterior M hMK hs hx (hMs.symm.subset hn))
  · ext s
    constructor
    · rintro ⟨hsP, hsM⟩
      obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ (s : Set E))
        (Finset.coe_nonempty.mpr (P.nonempty_of_mem_faces hsP)).convexHull
      exact K.face_mem_subcomplex_of_intrinsicInterior L hLK (hPK hsP) hx
        (hi.subset ⟨hPs.subset (P.convexHull_subset_space hsP (intrinsicInterior_subset hx)),
          hMs.subset (M.convexHull_subset_space hsM (intrinsicInterior_subset hx))⟩)
    · exact fun hs => ⟨hLP hs, hLM hs⟩

omit [FiniteDimensional ℝ E] in

theorem full_of_closed_side_partition
    (K L P M : SimplicialComplex ℝ E) (hLP : L ≤ P)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ L.vertices) → s ∈ L.faces)
    (hcover : ∀ s ∈ K.faces, s ∈ P.faces ∨ s ∈ M.faces)
    (hinter : P.faces ∩ M.faces = L.faces) :
    ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ P.vertices) → s ∈ P.faces := by
  intro s hs hvP
  rcases hcover s hs with hsP | hsM
  · exact hsP
  · apply hLP (hfull s hs ?_)
    intro v hv
    have hvM : v ∈ M.vertices :=
      M.down_closed hsM (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    exact hinter.subset ⟨hvP v hv, hvM⟩

end Geometry.SimplicialComplex
