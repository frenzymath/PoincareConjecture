import PoincareConjecture.Proofs.M76.Mathlib.ConeSimplex
import PoincareConjecture.Proofs.M76.Mathlib.RadialStar









set_option autoImplicit false

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E}

omit [NormedSpace ℝ E] in
private theorem subset_insert_erased (s : Finset E) :
    (s : Set E) ⊆ insert (0 : E) (s.erase 0 : Set E) := by
  intro x hx
  by_cases h : x = 0
  · exact Or.inl h
  · exact Or.inr (Finset.mem_erase.mpr ⟨h, hx⟩)

private theorem cone_face_independent
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    {s : Finset E} (hs : s.erase 0 = ∅ ∨ s.erase 0 ∈ K.faces) :
    AffineIndependent ℝ ((↑) : s → E) := by
  rcases hs with he | hface
  · apply (affineIndependent_of_subsingleton ℝ ((↑) : ↥({(0 : E)} : Set E) → E)).mono
    intro x hx
    change x = 0
    by_contra hx0
    have hmem : x ∈ s.erase 0 := Finset.mem_erase.mpr ⟨hx0, hx⟩
    exact Finset.notMem_empty x (he ▸ hmem)
  · exact (hlin _ hface).affineIndependent_insert_zero.mono (subset_insert_erased s)

private theorem cone_face_zero_mem
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    {s : Finset E} (hs : s.erase 0 = ∅ ∨ s.erase 0 ∈ K.faces)
    (hzero : (0 : E) ∈ convexHull ℝ (s : Set E)) : (0 : E) ∈ s := by
  by_contra hs0
  rw [Finset.erase_eq_of_notMem hs0] at hs
  rcases hs with he | hface
  · simp [he] at hzero
  · exact (hlin _ hface).zero_notMem_convexHull hzero

private theorem cone_face_base_point {s : Finset E}
    (hs : s.erase 0 = ∅ ∨ s.erase 0 ∈ K.faces) {x : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) (hx0 : x ≠ 0) :
    s.erase 0 ∈ K.faces ∧
      ∃ y ∈ convexHull ℝ (s.erase 0 : Set E), ∃ r ∈ Ioc (0 : ℝ) 1, x = r • y := by
  obtain ⟨y, hy, r, hr, he⟩ := exists_pos_smul_of_mem_convexHull_insert_zero
    (convexHull_mono (subset_insert_erased s) hx) hx0
  have hsK : s.erase 0 ∈ K.faces := hs.resolve_left (fun hempty => by simp [hempty] at hy)
  exact ⟨hsK, y, hy, r, hr, he⟩

private theorem cone_faces_inter_subset
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    {s t : Finset E} (hs : s.erase 0 = ∅ ∨ s.erase 0 ∈ K.faces)
    (ht : t.erase 0 = ∅ ∨ t.erase 0 ∈ K.faces) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
      convexHull ℝ ((s : Set E) ∩ t) := by
  rintro x ⟨hxs, hxt⟩
  by_cases hx0 : x = 0
  · subst x
    exact subset_convexHull ℝ _ ⟨cone_face_zero_mem hlin hs hxs, cone_face_zero_mem hlin ht hxt⟩
  obtain ⟨hsK, y, hy, a, ha, hxa⟩ := cone_face_base_point hs hxs hx0
  obtain ⟨htK, z, hz, b, hb, hxb⟩ := cone_face_base_point ht hxt hx0
  have hyx : NormedSpace.normalize y = NormedSpace.normalize x := by
    rw [hxa, normalize_smul_of_pos ha.1]
  have hzx : NormedSpace.normalize z = NormedSpace.normalize x := by
    rw [hxb, normalize_smul_of_pos hb.1]
  have hyz := hinj (convexHull_subset_space hsK hy) (convexHull_subset_space htK hz)
    (hyx.trans hzx.symm)
  have hyinter := K.inter_subset_convexHull hsK htK ⟨hy, hyz ▸ hz⟩
  have hsubset : (s.erase 0 : Set E) ∩ (t.erase 0 : Set E) ⊆ (s : Set E) ∩ t :=
    fun _ hv => ⟨Finset.erase_subset _ _ hv.1, Finset.erase_subset _ _ hv.2⟩
  have hybase : y ∈ convexHull ℝ ((s : Set E) ∩ t) := convexHull_mono hsubset hyinter
  by_cases hs0 : (0 : E) ∈ s
  · by_cases ht0 : (0 : E) ∈ t
    · rw [hxa]
      exact (convex_convexHull ℝ ((s : Set E) ∩ t)).smul_mem_of_zero_mem
        (subset_convexHull ℝ _ ⟨hs0, ht0⟩) hybase ⟨ha.1.le, ha.2⟩
    · have hxt' : x ∈ convexHull ℝ (t.erase 0 : Set E) := by
        simpa only [Finset.erase_eq_of_notMem ht0] using hxt
      have hxy := hinj (convexHull_subset_space htK hxt')
        (convexHull_subset_space hsK hy) hyx.symm
      simpa only [hxy] using hybase
  · have hxs' : x ∈ convexHull ℝ (s.erase 0 : Set E) := by
      simpa only [Finset.erase_eq_of_notMem hs0] using hxs
    have hxy := hinj (convexHull_subset_space hsK hxs')
      (convexHull_subset_space hsK hy) hyx.symm
    simpa only [hxy] using hybase




def coneAtZero (K : SimplicialComplex ℝ E)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) : SimplicialComplex ℝ E where
  faces := {s | s.Nonempty ∧ (s.erase 0 = ∅ ∨ s.erase 0 ∈ K.faces)}
  indep hs := cone_face_independent hlin hs.2
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    refine ⟨ht, ?_⟩
    by_cases he : t.erase 0 = ∅
    · exact Or.inl he
    · right
      rcases hs.2 with hs' | hs'
      · have hsub := Finset.erase_subset_erase (0 : E) hts
        rw [hs'] at hsub
        exact (he (Finset.subset_empty.mp hsub)).elim
      · exact K.down_closed hs' (Finset.erase_subset_erase _ hts)
          (Finset.nonempty_iff_ne_empty.mpr he)
  inter_subset_convexHull hs ht := cone_faces_inter_subset hlin hinj hs.2 ht.2



theorem mem_coneAtZero_faces
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) (s : Finset E) :
    s ∈ (K.coneAtZero hlin hinj).faces ↔
      s.Nonempty ∧ (s.erase 0 = ∅ ∨ s.erase 0 ∈ K.faces) := Iff.rfl



theorem zero_mem_coneAtZero_vertices
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) :
    (0 : E) ∈ (K.coneAtZero hlin hinj).vertices :=
  ⟨Finset.singleton_nonempty _, Or.inl (by simp)⟩



theorem le_coneAtZero
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) : K ≤ K.coneAtZero hlin hinj := by
  intro s hs
  have hs0 : (0 : E) ∉ s := fun h =>
    (hlin s hs).zero_notMem_convexHull (subset_convexHull ℝ _ h)
  exact ⟨K.nonempty_of_mem_faces hs, Or.inr (by rwa [Finset.erase_eq_of_notMem hs0])⟩



theorem link_coneAtZero
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) :
    (K.coneAtZero hlin hinj).link 0 = K := by
  ext s
  constructor
  · intro hs
    have hbase := hs.1.2
    rw [Finset.erase_eq_of_notMem hs.2.1] at hbase
    exact hbase.resolve_left hs.1.1.ne_empty
  · intro hs
    have hs0 : (0 : E) ∉ s := fun h =>
      (hlin s hs).zero_notMem_convexHull (subset_convexHull ℝ _ h)
    exact ⟨le_coneAtZero hlin hinj hs, hs0, Finset.insert_nonempty _ _,
      Or.inr (by rwa [Finset.erase_insert hs0])⟩



theorem closedStar_coneAtZero
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) :
    (K.coneAtZero hlin hinj).closedStar 0 = K.coneAtZero hlin hinj := by
  ext s
  refine ⟨fun hs => hs.1, fun hs => ⟨hs, Finset.insert_nonempty _ _, ?_⟩⟩
  simpa only [Finset.erase_insert_eq_erase] using hs.2

end Geometry.SimplicialComplex
