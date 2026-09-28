import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryEdgeDualInterval
import PoincareConjecture.Proofs.M76.PrimeReduction.TranslatedIntervalStarDisk
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalStarConeCarrier
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualFacetBoundary
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualSubcomplex










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K L : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype L.faces]




theorem exists_boundary_edge_dual_link_data
    (hLK : L ≤ K) (hLcard : ∀ t ∈ L.faces, t.card ≤ 3)
    {s : Finset E} (hs : s ∈ L.faces) (hscard : s.card = 2)
    (hends : (L.faceLink s).vertices.ncard = 2)
    (hI : IsFinitePLBallPair ℝ (K.faceLink s).space (L.faceLink s).space) :
    ∃ t u : Finset E, t ∈ L.faces ∧ u ∈ L.faces ∧
      t.card = 3 ∧ u.card = 3 ∧ s ⊆ t ∧ s ⊆ u ∧ t ≠ u ∧
      (∀ v ∈ L.faces, s ⊆ v → v.card = 3 → v = t ∨ v = u) ∧
      ((L.barycentricDualBlock s).link (s.centroid ℝ id)).space =
        {t.centroid ℝ id, u.centroid ℝ id} ∧
      IsFinitePLBallPair ℝ ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space
        {t.centroid ℝ id, u.centroid ℝ id} := by
  classical
  obtain ⟨a, b, hab, hverts⟩ := Set.ncard_eq_two.mp hends
  have ha : a ∈ (L.faceLink s).vertices := hverts.symm.subset (by simp)
  have hb : b ∈ (L.faceLink s).vertices := hverts.symm.subset (by simp)
  have hlinkle : L.faceLink s ≤ K.faceLink s :=
    fun _ ht => ⟨hLK ht.1, ht.2.1, hLK ht.2.2⟩
  have hLspace : (L.faceLink s).space = {a, b} := by
    apply subset_antisymm
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
      have hc := hLcard _ ht.2.2
      rw [Finset.card_union_of_disjoint ht.2.1, hscard] at hc
      have hpos := Finset.card_pos.mpr (L.nonempty_of_mem_faces ht.1)
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (show t.card = 1 by omega)
      have hxv : x = v := by
        simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using hxt
      subst x
      exact hverts.subset ht
    · exact hverts.symm.subset.trans (L.faceLink s).vertices_subset_space
  let t := s ∪ {a}
  let u := s ∪ {b}
  have ht : t ∈ L.faces := ha.2.2
  have hu : u ∈ L.faces := hb.2.2
  have hta : a ∉ s := (L.faceLink_vertices_subset s ha).2
  have hub : b ∉ s := (L.faceLink_vertices_subset s hb).2
  have htc : t.card = 3 := by
    change (s ∪ {a}).card = 3
    rw [Finset.union_singleton, Finset.card_insert_of_notMem hta, hscard]
  have huc : u.card = 3 := by
    change (s ∪ {b}).card = 3
    rw [Finset.union_singleton, Finset.card_insert_of_notMem hub, hscard]
  have hcofaces (v : Finset E) (hv : v ∈ L.faces) (hsv : s ⊆ v)
      (hvc : v.card = 3) : v = t ∨ v = u := by
    have hc : (v \ s).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsv, hvc, hscard]
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hc
    have hzlink : v \ s ∈ (L.faceLink s).faces := by
      refine ⟨L.down_closed hv Finset.sdiff_subset (Finset.card_pos.mp (by omega)), ?_, ?_⟩
      · exact Finset.disjoint_left.mpr (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx)
      · simpa only [Finset.union_sdiff_of_subset hsv] using hv
    have hzvert : z ∈ (L.faceLink s).vertices := by
      change {z} ∈ (L.faceLink s).faces
      rwa [hz] at hzlink
    have hzv : s ∪ {z} = v := by rw [← hz, Finset.union_sdiff_of_subset hsv]
    rcases hverts.subset hzvert with he | he
    · exact Or.inl (hzv.symm.trans (congrArg (fun w => s ∪ {w}) he))
    · exact Or.inr (hzv.symm.trans (congrArg (fun w => s ∪ {w}) he))
  have hMlink := L.barycentricDualBlock_link_space_of_paired_facet hLcard
    hs ht hu hscard htc huc Finset.subset_union_left Finset.subset_union_left hcofaces
  let ak : (K.faceLink s).vertices := ⟨a, hlinkle ha⟩
  let bk : (K.faceLink s).vertices := ⟨b, hlinkle hb⟩
  have hNlink := K.isFinitePLBallPair_dualLink_of_interval (hLK hs) ak bk
    (by simpa only [hLspace] using hI)
  refine ⟨t, u, ht, hu, htc, huc, Finset.subset_union_left,
    Finset.subset_union_left, ?_, hcofaces, hMlink, hNlink⟩
  intro he
  have hamem : a ∈ u := he ▸ (show a ∈ t from Finset.mem_union_right _ (by simp))
  rcases Finset.mem_union.mp hamem with has | hab'
  · exact hta has
  · exact hab (Finset.mem_singleton.mp hab')





theorem isFinitePLBallPair_boundary_edge_dual
    (hLK : L ≤ K) (hLcard : ∀ t ∈ L.faces, t.card ≤ 3)
    {s : Finset E} (hs : s ∈ L.faces) (hscard : s.card = 2)
    (hends : (L.faceLink s).vertices.ncard = 2)
    (hI : IsFinitePLBallPair ℝ (K.faceLink s).space (L.faceLink s).space) :
    IsFinitePLBallPair (ℝ × ℝ) (K.barycentricDualBlock s).space
      (((K.barycentricDualBlock s).link (s.centroid ℝ id)).space ∪
        (L.barycentricDualBlock s).space) := by
  obtain ⟨t, u, _, _, _, _, _, _, _, _, hMlink, hNlink⟩ :=
    K.exists_boundary_edge_dual_link_data L hLK hLcard hs hscard hends hI
  have hMne : ((L.barycentricDualBlock s).link (s.centroid ℝ id)).space.Nonempty := by
    rw [hMlink]
    simp
  have hMcone := (L.barycentricDualBlock s).closedStar_space_eq_convexJoin_link
    (L.faceCentroid_mem_barycentricDualBlock_vertices hs) hMne
  rw [L.barycentricDualBlock_closedStar_faceCentroid hs, hMlink] at hMcone
  have hball := (K.barycentricDualBlock s).isFinitePLBallPair_closedStar_of_interval
    (K.barycentricDualBlock_finite s) (K.faceCentroid_mem_barycentricDualBlock_vertices (hLK hs))
    hNlink
  change IsFinitePLBallPair (ℝ × ℝ)
    ((K.barycentricDualBlock s).closedStar (s.centroid ℝ id)).space
    (((K.barycentricDualBlock s).link (s.centroid ℝ id)).space ∪
      convexJoin ℝ {s.centroid ℝ id} {t.centroid ℝ id, u.centroid ℝ id}) at hball
  simpa only [K.barycentricDualBlock_closedStar_faceCentroid (hLK hs),
    ← hMcone] using hball

end Geometry.SimplicialComplex
