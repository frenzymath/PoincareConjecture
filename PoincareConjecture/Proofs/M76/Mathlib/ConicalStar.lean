import PoincareConjecture.Proofs.M76.Mathlib.SimplicialCone

set_option autoImplicit false

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E}

theorem coneAtZero_vertices
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) :
    (K.coneAtZero hlin hinj).vertices = insert (0 : E) K.vertices := by
  ext x
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      have hbase := hx.2
      have hnot : (0 : E) ∉ ({x} : Finset E) := by simpa using Ne.symm hx0
      rw [Finset.erase_eq_of_notMem hnot] at hbase
      exact hbase.resolve_left (Finset.singleton_nonempty x).ne_empty
  · rintro (hx | hx)
    · subst x
      exact zero_mem_coneAtZero_vertices hlin hinj
    · exact le_coneAtZero hlin hinj hx

theorem insert_zero_mem_coneAtZero_faces
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    {s : Finset E} (hs : s ∈ K.faces) : insert (0 : E) s ∈ (K.coneAtZero hlin hinj).faces := by
  have hs0 : (0 : E) ∉ s := fun h =>
    (hlin s hs).zero_notMem_convexHull (subset_convexHull ℝ _ h)
  exact ⟨Finset.insert_nonempty _ _, Or.inr (by rwa [Finset.erase_insert hs0])⟩

theorem finite_coneAtZero_faces (hK : K.faces.Finite)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) :
    (K.coneAtZero hlin hinj).faces.Finite := by
  apply ((hK.union (hK.image (fun s => insert (0 : E) s))).union
    (Set.finite_singleton ({0} : Finset E))).subset
  intro s hs
  rcases hs.2 with he | hface
  · right
    rcases (Finset.erase_eq_empty_iff s 0).mp he with he | he
    · exact (hs.1.ne_empty he).elim
    · exact he
  · left
    by_cases hs0 : (0 : E) ∈ s
    · exact Or.inr ⟨s.erase 0, hface, Finset.insert_erase hs0⟩
    · exact Or.inl (by simpa only [Finset.erase_eq_of_notMem hs0] using hface)

theorem coneAtZero_link_eq_closedStar (K : SimplicialComplex ℝ E)
    (hzero : (0 : E) ∈ K.vertices) :
    (K.link 0).coneAtZero (fun _ hs => linearIndependent_of_mem_link_zero hs)
      (injOn_normalize_link K) = K.closedStar 0 := by
  ext s
  constructor
  · intro hs
    rcases hs.2 with he | hlink
    · rcases (Finset.erase_eq_empty_iff s 0).mp he with he | he
      · exact (hs.1.ne_empty he).elim
      · subst s
        refine ⟨hzero, ?_⟩
        rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self (0 : E))]
        exact hzero
    · have hsubset : s ⊆ insert (0 : E) (s.erase 0) := Finset.insert_erase_subset _ _
      refine ⟨K.down_closed hlink.2.2 hsubset hs.1, ?_⟩
      exact K.down_closed hlink.2.2
        ((Finset.insert_subset_insert 0 hsubset).trans (by simp)) (Finset.insert_nonempty _ _)
  · intro hs
    refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
    by_cases he : s.erase 0 = ∅
    · exact Or.inl he
    · right
      exact ⟨K.down_closed hs.1 (Finset.erase_subset _ _) (Finset.nonempty_iff_ne_empty.mpr he),
        Finset.notMem_erase _ _,
        K.down_closed hs.2 (Finset.insert_subset_insert 0 (Finset.erase_subset _ _))
          (Finset.insert_nonempty _ _)⟩

end Geometry.SimplicialComplex
