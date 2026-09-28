


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.Subdivision
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.Intersections













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u v

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]



theorem exists_finite_edge_refinement {I : Type v} [Finite I]
    (e : I → SmoothEdge M)
    (he : ∀ i, InjOn (e i).map (Icc (0 : ℝ) 1))
    (hfinite : ∀ i j, i ≠ j →
      ((e i).map '' Icc (0 : ℝ) 1 ∩ (e j).map '' Icc (0 : ℝ) 1).Finite) :
    ∃ (n : I → ℕ) (c : ∀ i, Fin (n i + 1) → ℝ)
      (piece : ∀ i, Fin (n i) → SmoothEdge M),
      (∀ i, 0 < n i ∧ StrictMono (c i) ∧ c i 0 = 0 ∧ c i (Fin.last (n i)) = 1 ∧
        (∀ k t, (piece i k).map t =
          (e i).map (c i k.castSucc + t * (c i k.succ - c i k.castSucc))) ∧
        (∀ k, InjOn (piece i k).map (Icc (0 : ℝ) 1)) ∧
        (⋃ k, (piece i k).map '' Icc (0 : ℝ) 1) = (e i).map '' Icc (0 : ℝ) 1 ∧
        (∀ k l, k < l → (piece i k).map '' Icc (0 : ℝ) 1 ∩
          (piece i l).map '' Icc (0 : ℝ) 1 ⊆ {(e i).map (c i k.succ)}) ∧
        (∀ k, Disjoint ((piece i k).map '' Ioo (0 : ℝ) 1)
          ((e i).map '' range (c i)))) ∧
      (∀ i j, i ≠ j → ∀ k, Disjoint ((piece i k).map '' Ioo (0 : ℝ) 1)
        ((e j).map '' Icc (0 : ℝ) 1)) ∧
      (∀ p q : Σ i, Fin (n i), p ≠ q →
        (piece p.1 p.2).map '' Icc (0 : ℝ) 1 ∩
          (piece q.1 q.2).map '' Icc (0 : ℝ) 1 ⊆
        {(piece p.1 p.2).map 0, (piece p.1 p.2).map 1} ∩
          {(piece q.1 q.2).map 0, (piece q.1 q.2).map 1}) := by
  classical
  let crossings (i j : I) : Set ℝ :=
    {t | t ∈ Icc (0 : ℝ) 1 ∧ (e i).map t ∈ (e j).map '' Icc (0 : ℝ) 1}
  have hcrossings (i j : I) (hij : i ≠ j) : (crossings i j).Finite := by
    apply Finite.of_finite_image (f := (e i).map)
    · apply (hfinite i j hij).subset
      rintro x ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht.1, rfl⟩, ht.2⟩
    · exact (he i).mono (fun _ ht => ht.1)
  let cuts (i : I) : Set ℝ := ⋃ j : {j : I // i ≠ j}, crossings i j
  have hcuts (i : I) : (cuts i).Finite := finite_iUnion (fun j => hcrossings i j j.2)
  have hbounds (i : I) : ∀ t ∈ (hcuts i).toFinset, t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    obtain ⟨j, hj⟩ := mem_iUnion.mp ((hcuts i).mem_toFinset.mp ht)
    exact hj.1
  choose n c piece hn hc hzero hone hrange hmap hinj hcover hmeet havoid using
    fun i => (e i).exists_finite_subdivision (he i) (hcuts i).toFinset (hbounds i)
  have hother : ∀ i j, i ≠ j → ∀ k, Disjoint ((piece i k).map '' Ioo (0 : ℝ) 1)
      ((e j).map '' Icc (0 : ℝ) 1) := by
    intro i j hij k
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hx' : x ∈ (e i).map '' Icc (0 : ℝ) 1 := by
      rw [← hcover i]
      exact mem_iUnion.mpr ⟨k, image_mono Ioo_subset_Icc_self hx⟩
    obtain ⟨t, ht, rfl⟩ := hx'
    have htcut : t ∈ range (c i) := by
      rw [hrange i]
      apply Or.inl
      exact (hcuts i).mem_toFinset.mpr (mem_iUnion.mpr ⟨⟨j, hij⟩, ht, hy⟩)
    exact Set.disjoint_left.mp (havoid i k) hx ⟨t, htcut, rfl⟩
  have hdisjoint : ∀ p q : Σ i, Fin (n i), p ≠ q →
      Disjoint ((piece p.1 p.2).map '' Ioo (0 : ℝ) 1)
        ((piece q.1 q.2).map '' Icc (0 : ℝ) 1) := by
    rintro ⟨i, k⟩ ⟨j, l⟩ hpq
    by_cases hij : i = j
    · subst j
      have hkl : k ≠ l := fun h => hpq (h ▸ rfl)
      apply Set.disjoint_left.mpr
      intro x hx hy
      have hx' := image_mono Ioo_subset_Icc_self hx
      rcases lt_or_gt_of_ne hkl with hlt | hgt
      · have hpoint := hmeet i k l hlt ⟨hx', hy⟩
        exact Set.disjoint_left.mp (havoid i k) hx
          ⟨c i k.succ, mem_range_self _, (mem_singleton_iff.mp hpoint).symm⟩
      · have hpoint := hmeet i l k hgt ⟨hy, hx'⟩
        exact Set.disjoint_left.mp (havoid i k) hx
          ⟨c i l.succ, mem_range_self _, (mem_singleton_iff.mp hpoint).symm⟩
    · apply (hother i j hij k).mono_right
      rw [← hcover j]
      exact subset_iUnion (fun l => (piece j l).map '' Icc (0 : ℝ) 1) l
  have hendpoint (p q : Σ i, Fin (n i)) (hpq : p ≠ q) {x : M}
      (hx : x ∈ (piece p.1 p.2).map '' Icc (0 : ℝ) 1)
      (hy : x ∈ (piece q.1 q.2).map '' Icc (0 : ℝ) 1) :
      x ∈ ({(piece p.1 p.2).map 0, (piece p.1 p.2).map 1} : Set M) := by
    obtain ⟨t, ht, rfl⟩ := hx
    by_cases hzero : t = 0
    · simp [hzero]
    by_cases hone : t = 1
    · simp [hone]
    exact False.elim (Set.disjoint_left.mp (hdisjoint p q hpq)
      ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm hzero), lt_of_le_of_ne ht.2 hone⟩, rfl⟩ hy)
  exact ⟨n, c, piece, fun i => ⟨hn i, hc i, hzero i, hone i, hmap i, hinj i,
    hcover i, hmeet i, havoid i⟩, hother,
    fun p q hpq x hx => ⟨hendpoint p q hpq hx.1 hx.2,
      hendpoint q p hpq.symm hx.2 hx.1⟩⟩

end PoincareConjecture.Topology.Surface
