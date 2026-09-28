import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ComplementaryTriangleGraph
import PoincareConjecture.Proofs.M76.Mathlib.VertexInducedSubcomplex













set_option autoImplicit false
open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K L : SimplicialComplex ℝ E)


def markedTriangleGraph : SimpleGraph (Triangle K.toPreAbstractSimplicialComplex) where
  Adj q r := q ≠ r ∧ ∃ s ∈ K.faces, s.card = 2 ∧ s ∉ L.faces ∧ s ⊆ q.val ∧ s ⊆ r.val
  symm := ⟨by
    rintro q r ⟨hqr, s, hs, hcard, hmark, hsq, hsr⟩
    exact ⟨hqr.symm, s, hs, hcard, hmark, hsr, hsq⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩


def markedTriangleComponent (C : (K.markedTriangleGraph L).ConnectedComponent) :
    SimplicialComplex ℝ E where
  faces := {s | s ∈ K.faces ∧ ∃ t ∈ C.supp, s ⊆ t.val}
  indep hs := K.indep hs.1
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
    intro r hrs hr
    obtain ⟨t, ht, hst⟩ := hs.2
    exact ⟨K.down_closed hs.1 hrs hr, t, ht, hrs.trans hst⟩
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

theorem markedTriangleComponent_le (C : (K.markedTriangleGraph L).ConnectedComponent) :
    K.markedTriangleComponent L C ≤ K := fun _ hs ↦ hs.1

theorem markedTriangleComponent_finite (C : (K.markedTriangleGraph L).ConnectedComponent)
    (hK : K.faces.Finite) : (K.markedTriangleComponent L C).faces.Finite :=
  hK.subset (K.markedTriangleComponent_le L C)

theorem markedTriangleComponent_triangle_iff
    (C : (K.markedTriangleGraph L).ConnectedComponent)
    (t : Triangle K.toPreAbstractSimplicialComplex) :
    t.val ∈ (K.markedTriangleComponent L C).faces ↔ t ∈ C.supp := by
  constructor
  · rintro ⟨_, u, hu, htu⟩
    have heq : t = u := Subtype.ext
      (Finset.eq_of_subset_of_card_le htu (by rw [t.property.2, u.property.2]))
    exact heq.symm ▸ hu
  · exact fun ht ↦ ⟨t.property.1, t, ht, subset_rfl⟩

theorem markedTriangleComponent_pure
    (C : (K.markedTriangleGraph L).ConnectedComponent) :
    ∀ s ∈ (K.markedTriangleComponent L C).faces,
      ∃ t ∈ (K.markedTriangleComponent L C).faces, t.card = 3 ∧ s ⊆ t := by
  rintro s ⟨_, t, ht, hst⟩
  exact ⟨t.val, (K.markedTriangleComponent_triangle_iff L C t).mpr ht,
    t.property.2, hst⟩



theorem markedTriangleComponent_unmarked_coface
    (C : (K.markedTriangleGraph L).ConnectedComponent)
    {s t : Finset E} (hs : s ∈ (K.markedTriangleComponent L C).faces)
    (hsc : s.card = 2) (hmark : s ∉ L.faces)
    (ht : t ∈ K.faces) (htc : t.card = 3) (hst : s ⊆ t) :
    t ∈ (K.markedTriangleComponent L C).faces := by
  obtain ⟨u, hu, hsu⟩ := hs.2
  let q : Triangle K.toPreAbstractSimplicialComplex := ⟨t, ht, htc⟩
  apply (K.markedTriangleComponent_triangle_iff L C q).mpr
  by_cases heq : u = q
  · exact heq ▸ hu
  · exact C.mem_supp_of_adj_mem_supp hu ⟨heq, s, hs.1, hsc, hmark, hsu, hst⟩

theorem markedTriangleComponent_unmarked_cofaces
    (C : (K.markedTriangleGraph L).ConnectedComponent)
    {s : Finset E} (hs : s ∈ (K.markedTriangleComponent L C).faces)
    (hsc : s.card = 2) (hmark : s ∉ L.faces) :
    {t : Finset E | t ∈ (K.markedTriangleComponent L C).faces ∧ t.card = 3 ∧ s ⊆ t} =
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t} := by
  ext t
  constructor
  · exact fun ht ↦ ⟨ht.1.1, ht.2⟩
  · exact fun ht ↦ ⟨K.markedTriangleComponent_unmarked_coface L C hs hsc hmark
      ht.1 ht.2.1 ht.2.2, ht.2⟩


theorem markedTriangleComponent_one_coface_marked
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (C : (K.markedTriangleGraph L).ConnectedComponent)
    {s : Finset E} (hs : s ∈ (K.markedTriangleComponent L C).faces) (hsc : s.card = 2)
    (hone : {t : Finset E | t ∈ (K.markedTriangleComponent L C).faces ∧
      t.card = 3 ∧ s ⊆ t}.ncard = 1) : s ∈ L.faces := by
  by_contra hmark
  rw [K.markedTriangleComponent_unmarked_cofaces L C hs hsc hmark,
    hcofaces s hs.1 hsc] at hone
  omega


theorem exists_markedTriangleComponent_of_face
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    {s : Finset E} (hs : s ∈ K.faces) :
    ∃ C : (K.markedTriangleGraph L).ConnectedComponent,
      s ∈ (K.markedTriangleComponent L C).faces := by
  obtain ⟨t, ht, htc, hst⟩ := hpure s hs
  let q : Triangle K.toPreAbstractSimplicialComplex := ⟨t, ht, htc⟩
  exact ⟨(K.markedTriangleGraph L).connectedComponentMk q,
    hs, q, by simp, hst⟩

theorem markedTriangleComponent_space
    (C : (K.markedTriangleGraph L).ConnectedComponent) :
    (K.markedTriangleComponent L C).space =
      ⋃ t : C, convexHull ℝ (t.val.val : Set E) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨t, ht, hst⟩ := hs.2
    exact mem_iUnion.mpr ⟨⟨t, ht⟩, convexHull_mono hst hxs⟩
  · intro x hx
    obtain ⟨t, hxt⟩ := mem_iUnion.mp hx
    exact (K.markedTriangleComponent L C).convexHull_subset_space
      ((K.markedTriangleComponent_triangle_iff L C t.val).mpr t.property) hxt



theorem markedTriangleComponent_isConnected
    (C : (K.markedTriangleGraph L).ConnectedComponent) :
    IsConnected (K.markedTriangleComponent L C).space := by
  rw [K.markedTriangleComponent_space L C]
  let : Nonempty C := C.connected_toSimpleGraph.nonempty
  apply IsConnected.iUnion_of_reflTransGen
  · intro t
    obtain ⟨p, hp⟩ := K.nonempty_of_mem_faces t.val.property.1
    exact (convex_convexHull ℝ (t.val.val : Set E)).isConnected
      ⟨p, subset_convexHull ℝ _ hp⟩
  · intro t u
    have hreach := (SimpleGraph.reachable_iff_reflTransGen t u).mp
      (C.connected_toSimpleGraph.preconnected t u)
    apply Relation.ReflTransGen.mono ?_ t u hreach
    intro q r hqr
    obtain ⟨_, s, hs, _, _, hsq, hsr⟩ := hqr
    obtain ⟨p, hp⟩ := K.nonempty_of_mem_faces hs
    exact ⟨p, subset_convexHull ℝ _ (hsq hp), subset_convexHull ℝ _ (hsr hp)⟩



theorem markedTriangleComponent_edge_coface_count
    (hK : K.faces.Finite)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (C : (K.markedTriangleGraph L).ConnectedComponent)
    {s : Finset E} (hs : s ∈ (K.markedTriangleComponent L C).faces) (hsc : s.card = 2) :
    {t : Finset E | t ∈ (K.markedTriangleComponent L C).faces ∧
      t.card = 3 ∧ s ⊆ t}.ncard = 1 ∨
    {t : Finset E | t ∈ (K.markedTriangleComponent L C).faces ∧
      t.card = 3 ∧ s ⊆ t}.ncard = 2 := by
  have hfin : {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.Finite :=
    hK.subset fun _ ht ↦ ht.1
  have hsub : {t : Finset E | t ∈ (K.markedTriangleComponent L C).faces ∧
      t.card = 3 ∧ s ⊆ t} ⊆ {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t} :=
    fun _ ht ↦ ⟨ht.1.1, ht.2⟩
  have hle := ncard_le_ncard hsub hfin
  rw [hcofaces s hs.1 hsc] at hle
  have hne : {t : Finset E | t ∈ (K.markedTriangleComponent L C).faces ∧
      t.card = 3 ∧ s ⊆ t}.Nonempty := by
    obtain ⟨t, ht, htc, hst⟩ := K.markedTriangleComponent_pure L C s hs
    exact ⟨t, ht, htc, hst⟩
  have hpos := hne.ncard_pos (hfin.subset hsub)
  omega

theorem markedTriangleComponents_cover
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t) :
    (⋃ C : (K.markedTriangleGraph L).ConnectedComponent,
      (K.markedTriangleComponent L C).space) = K.space := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨C, hx⟩ := mem_iUnion.mp hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact K.convexHull_subset_space hs.1 hxs
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨C, hsC⟩ := K.exists_markedTriangleComponent_of_face L hpure hs
    exact mem_iUnion.mpr ⟨C, (K.markedTriangleComponent L C).convexHull_subset_space hsC hxs⟩

end Geometry.SimplicialComplex
