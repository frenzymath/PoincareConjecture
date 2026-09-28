import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SurfaceDualBlockIncidence
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualFacetInterval

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E) [Fintype K.faces]

theorem dualEdge_inter_other_vertex_blocks
    (hbound : ∀ v ∈ K.faces, v.card ≤ 3)
    {p q : E} (hpq : p ≠ q) {t u : Finset E}
    (ht : t ∈ K.faces) (hu : u ∈ K.faces) (htc : t.card = 3) (huc : u.card = 3)
    (hpt : ({p, q} : Finset E) ⊆ t) (hpu : ({p, q} : Finset E) ⊆ u)
    (hcofaces : ∀ v ∈ K.faces, ({p, q} : Finset E) ⊆ v →
      v.card = 3 → v = t ∨ v = u) :
    (K.barycentricDualBlock {p, q}).space ∩
        (⋃ z ∈ K.vertices \ {p, q}, (K.barycentricDualBlock {z}).space) =
      {t.centroid ℝ id, u.centroid ℝ id} := by
  classical
  apply Subset.antisymm
  · intro x hx
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hx.2
    let s : Finset E := ({p, q} : Finset E) ∪ {z}
    have hzs : z ∉ ({p, q} : Finset E) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, mem_insert_iff,
        mem_singleton_iff] using hz.2
    have hsc : s.card = 3 := by
      change (({p, q} : Finset E) ∪ {z}).card = 3
      rw [Finset.union_singleton, Finset.card_insert_of_notMem hzs,
        Finset.card_pair hpq]
    have hxs : x ∈ (K.barycentricDualBlock s).space :=
      (K.barycentricDualBlock_space_inter {p, q} {z}).subset ⟨hx.1, hxz⟩
    have hs : s ∈ K.faces := by
      by_contra hs
      have hsn : s.Nonempty := Finset.card_pos.mp (by omega)
      rw [K.barycentricDualBlock_space_eq_empty_of_not_face hsn hs] at hxs
      exact hxs
    have hmax (v : Finset E) (hv : v ∈ K.faces) (hsv : s ⊆ v) : v = s := by
      exact (Finset.eq_of_subset_of_card_le hsv (by rw [hsc]; exact hbound v hv)).symm
    have hxc : x = s.centroid ℝ id := by
      simpa only [K.barycentricDualBlock_space_eq_centroid_of_maximal hs hmax,
        mem_singleton_iff] using hxs
    rcases hcofaces s hs Finset.subset_union_left hsc with hst | hsu
    · exact Or.inl (hxc.trans (congrArg (fun v : Finset E => v.centroid ℝ id) hst))
    · exact Or.inr (hxc.trans (congrArg (fun v : Finset E => v.centroid ℝ id) hsu))
  · have hmark (v : Finset E) (hv : v ∈ K.faces) (hvc : v.card = 3)
        (hpv : ({p, q} : Finset E) ⊆ v) :
        v.centroid ℝ id ∈ (K.barycentricDualBlock {p, q}).space ∩
          (⋃ z ∈ K.vertices \ {p, q}, (K.barycentricDualBlock {z}).space) := by
      have hnsub : ¬v ⊆ ({p, q} : Finset E) := by
        intro h
        have hcard := Finset.card_le_card h
        rw [hvc, Finset.card_pair hpq] at hcard
        omega
      obtain ⟨z, hzv, hzp⟩ := Finset.not_subset.mp hnsub
      have hz : z ∈ K.vertices \ ({p, q} : Set E) := by
        refine ⟨K.face_subset_vertices hv hzv, ?_⟩
        simpa only [Finset.mem_insert, Finset.mem_singleton, mem_insert_iff,
          mem_singleton_iff] using hzp
      have hc : v.centroid ℝ id ∈ (K.barycentricDualBlock v).space :=
        (K.barycentricDualBlock v).vertices_subset_space
          (K.faceCentroid_mem_barycentricDualBlock_vertices hv)
      exact ⟨space_subset_of_le (K.barycentricDualBlock_antitone hpv) hc,
        mem_iUnion₂.mpr ⟨z, hz, space_subset_of_le
          (K.barycentricDualBlock_antitone (Finset.singleton_subset_iff.mpr hzv)) hc⟩⟩
    rintro x (rfl | rfl)
    · exact hmark t ht htc hpt
    · exact hmark u hu huc hpu

variable [FiniteDimensional ℝ E]

theorem exists_surface_dual_edge_interval
    (hbound : ∀ v ∈ K.faces, v.card ≤ 3)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {v : Finset E | v ∈ K.faces ∧ v.card = 3 ∧ e ⊆ v}.ncard = 2)
    {p q : E} (hpq : p ≠ q) (he : ({p, q} : Finset E) ∈ K.faces) :
    ∃ t ∈ K.faces, ∃ u ∈ K.faces,
      t.card = 3 ∧ u.card = 3 ∧ ({p, q} : Finset E) ⊆ t ∧
      ({p, q} : Finset E) ⊆ u ∧ t.centroid ℝ id ≠ u.centroid ℝ id ∧
      IsFinitePLBallPair ℝ (K.barycentricDualBlock {p, q}).space
        {t.centroid ℝ id, u.centroid ℝ id} ∧
      ({p, q} : Finset E).centroid ℝ id ∈ (K.barycentricDualBlock {p, q}).space \
        {t.centroid ℝ id, u.centroid ℝ id} ∧
      (K.barycentricDualBlock {p, q}).space ∩
          (⋃ z ∈ K.vertices \ {p, q}, (K.barycentricDualBlock {z}).space) =
        {t.centroid ℝ id, u.centroid ℝ id} := by
  obtain ⟨t, u, htu, hset⟩ := Set.ncard_eq_two.mp
    (hcofaces {p, q} he (Finset.card_pair hpq))
  have ht : t ∈ K.faces ∧ t.card = 3 ∧ ({p, q} : Finset E) ⊆ t := by
    apply hset.symm.subset
    exact Or.inl rfl
  have hu : u ∈ K.faces ∧ u.card = 3 ∧ ({p, q} : Finset E) ⊆ u := by
    apply hset.symm.subset
    exact Or.inr rfl
  have hexhaust (v : Finset E) (hv : v ∈ K.faces)
      (hsv : ({p, q} : Finset E) ⊆ v) (hvc : v.card = 3) : v = t ∨ v = u :=
    hset.subset ⟨hv, hvc, hsv⟩
  have hcent : t.centroid ℝ id ≠ u.centroid ℝ id := by
    intro h
    have heq : (⟨t, ht.1⟩ : K.faces) = ⟨u, hu.1⟩ := K.faceCentroid_injective h
    exact htu (congrArg Subtype.val heq)
  have hpair := K.isFinitePLBallPair_barycentricDualBlock_of_paired_facet
    (n := 2) hbound he ht.1 hu.1 (Finset.card_pair hpq) ht.2.1 hu.2.1
    ht.2.2 hu.2.2 htu hexhaust
  exact ⟨t, ht.1, u, hu.1, ht.2.1, hu.2.1, ht.2.2, hu.2.2, hcent, hpair.1,
    hpair.2, K.dualEdge_inter_other_vertex_blocks hbound hpq ht.1 hu.1 ht.2.1 hu.2.1
      ht.2.2 hu.2.2 hexhaust⟩

end Geometry.SimplicialComplex
