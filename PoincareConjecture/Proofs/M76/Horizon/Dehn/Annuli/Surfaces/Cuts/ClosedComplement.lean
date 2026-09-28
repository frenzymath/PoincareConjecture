import PoincareConjecture.Proofs.M76.Mathlib.BarycentricNeighborhoodCarrier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SurfaceEulerValuation












set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K N : SimplicialComplex ℝ E)


def closedFaceComplement : SimplicialComplex ℝ E where
  faces := {s | s ∈ K.faces ∧ ∃ t ∈ K.faces, t ∉ N.faces ∧ s ⊆ t}
  indep hs := K.indep hs.1
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
    intro r hrs hr
    obtain ⟨t, ht, htN, hst⟩ := hs.2
    exact ⟨K.down_closed hs.1 hrs hr, t, ht, htN, hrs.trans hst⟩
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

theorem closedFaceComplement_le : K.closedFaceComplement N ≤ K := fun _ hs ↦ hs.1

theorem closedFaceComplement_finite (hK : K.faces.Finite) :
    (K.closedFaceComplement N).faces.Finite :=
  hK.subset (K.closedFaceComplement_le N)

theorem closedFaceComplement_cover (hNK : N ≤ K) :
    N.faces ∪ (K.closedFaceComplement N).faces = K.faces := by
  ext s
  constructor
  · rintro (hs | hs)
    · exact hNK hs
    · exact hs.1
  · intro hs
    by_cases hsN : s ∈ N.faces
    · exact Or.inl hsN
    · exact Or.inr ⟨hs, s, hs, hsN, subset_rfl⟩

theorem closedFaceComplement_space :
    (K.closedFaceComplement N).space = ⋃ t ∈ K.faces \ N.faces,
      convexHull ℝ (t : Set E) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨t, ht, htN, hst⟩ := hs.2
    exact mem_iUnion₂.mpr ⟨t, ⟨ht, htN⟩, convexHull_mono hst hxs⟩
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    exact (K.closedFaceComplement N).convexHull_subset_space
      ⟨ht.1, t, ht.1, ht.2, subset_rfl⟩ hxt

theorem closedFaceComplement_space_cover (hNK : N ≤ K) :
    N.space ∪ (K.closedFaceComplement N).space = K.space := by
  apply Subset.antisymm
  · rintro x (hx | hx)
    · obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
      exact K.convexHull_subset_space (hNK hs) hxs
    · obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
      exact K.convexHull_subset_space hs.1 hxs
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    rcases (K.closedFaceComplement_cover N hNK).symm.subset hs with hs | hs
    · exact Or.inl (N.convexHull_subset_space hs hxs)
    · exact Or.inr ((K.closedFaceComplement N).convexHull_subset_space hs hxs)



theorem closedFaceComplement_euler (hK : K.faces.Finite) (hNK : N ≤ K) :
    K.surfaceEulerCount + (N ⊓ K.closedFaceComplement N).surfaceEulerCount =
      N.surfaceEulerCount + (K.closedFaceComplement N).surfaceEulerCount :=
  N.surfaceEulerCount_union_add_inter (K.closedFaceComplement N) K
    (hK.subset hNK) (K.closedFaceComplement_finite N hK)
    (K.closedFaceComplement_cover N hNK).symm

theorem closedFaceComplement_triangle_iff
    (hdim : ∀ s ∈ K.faces, s.card ≤ 3) {t : Finset E} (htc : t.card = 3) :
    t ∈ (K.closedFaceComplement N).faces ↔ t ∈ K.faces ∧ t ∉ N.faces := by
  constructor
  · rintro ⟨ht, u, hu, huN, htu⟩
    have heq : t = u := Finset.eq_of_subset_of_card_le htu (by simpa [htc] using hdim u hu)
    exact ⟨ht, heq.symm ▸ huN⟩
  · exact fun ht ↦ ⟨ht.1, t, ht.1, ht.2, subset_rfl⟩

theorem closedFaceComplement_pure
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t) :
    ∀ s ∈ (K.closedFaceComplement N).faces,
      ∃ t ∈ (K.closedFaceComplement N).faces, t.card = 3 ∧ s ⊆ t := by
  rintro s ⟨hs, u, hu, huN, hsu⟩
  obtain ⟨t, ht, htc, hut⟩ := hpure u hu
  have htN : t ∉ N.faces := fun htN ↦
    huN (N.down_closed htN hut (K.nonempty_of_mem_faces hu))
  exact ⟨t, ⟨ht, t, ht, htN, subset_rfl⟩, htc, hsu.trans hut⟩

theorem closedFaceComplement_inter_dim
    (hdim : ∀ s ∈ K.faces, s.card ≤ 3) :
    ∀ s ∈ (N ⊓ K.closedFaceComplement N).faces, s.card ≤ 2 := by
  intro s hs
  have hsc := hdim s hs.2.1
  by_contra hnot
  have hthree : s.card = 3 := by omega
  exact ((K.closedFaceComplement_triangle_iff N hdim hthree).mp hs.2).2 hs.1

open Classical in


theorem closedFaceComplement_edge_coface_count
    (hK : K.faces.Finite) (hNK : N ≤ K)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hNpure : ∀ s ∈ N.faces, ∃ t ∈ N.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    {s : Finset E} (hs : s ∈ (K.closedFaceComplement N).faces) (hsc : s.card = 2) :
    {t : Finset E | t ∈ (K.closedFaceComplement N).faces ∧
      t.card = 3 ∧ s ⊆ t}.ncard = if s ∈ N.faces then 1 else 2 := by
  classical
  have hdim (t : Finset E) (ht : t ∈ K.faces) : t.card ≤ 3 := by
    obtain ⟨u, _, huc, htu⟩ := hpure t ht
    exact (Finset.card_le_card htu).trans_eq huc
  let S := {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}
  let T := {t : Finset E | t ∈ (K.closedFaceComplement N).faces ∧
    t.card = 3 ∧ s ⊆ t}
  have hST : S.Finite := hK.subset fun _ ht ↦ ht.1
  have hsub : T ⊆ S := fun _ ht ↦ ⟨ht.1.1, ht.2⟩
  have hcount : S.ncard = 2 := hcofaces s hs.1 hsc
  change T.ncard = _
  by_cases hsN : s ∈ N.faces
  · rw [if_pos hsN]
    obtain ⟨r, hr, hrc, hsr⟩ := hNpure s hsN
    obtain ⟨u, hu, huc, hsu⟩ := K.closedFaceComplement_pure N hpure s hs
    have huN := ((K.closedFaceComplement_triangle_iff N hdim huc).mp hu).2
    have hru : r ≠ u := fun he ↦ huN (he ▸ hr)
    have hpair : S = {r, u} := by
      apply (eq_of_subset_of_ncard_le ?_ ?_ hST).symm
      · rintro t (rfl | rfl)
        · exact ⟨hNK hr, hrc, hsr⟩
        · exact ⟨hu.1, huc, hsu⟩
      · rw [hcount, ncard_pair hru]
    have hT : T = {u} := by
      ext t
      constructor
      · intro ht
        rcases hpair.subset (hsub ht) with rfl | rfl
        · exact (((K.closedFaceComplement_triangle_iff N hdim hrc).mp ht.1).2 hr).elim
        · rfl
      · rintro rfl
        exact ⟨hu, huc, hsu⟩
    rw [hT, ncard_singleton]
  · rw [if_neg hsN]
    have hTS : T = S := by
      apply Subset.antisymm hsub
      intro t ht
      have htN : t ∉ N.faces := fun htN ↦
        hsN (N.down_closed htN ht.2.2 (K.nonempty_of_mem_faces hs.1))
      exact ⟨(K.closedFaceComplement_triangle_iff N hdim ht.2.1).mpr ⟨ht.1, htN⟩, ht.2⟩
    exact hTS ▸ hcount



theorem closedFaceComplement_barycentric_disjoint [Fintype K.faces]
    (L : SimplicialComplex ℝ E) [Finite L.faces] (hLK : L ≤ K) :
    Disjoint (K.barycentricSubdivision.closedFaceComplement
      (K.barycentricNeighborhood L)).space L.space := by
  rw [disjoint_left]
  intro x hx hxL
  rw [closedFaceComplement_space] at hx
  obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
  exact ht.2 (K.mem_barycentricNeighborhood_of_inter_nonempty hLK ht.1 ⟨x, hxt, hxL⟩)

end Geometry.SimplicialComplex
