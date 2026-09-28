import PoincareConjecture.Proofs.M76.Mathlib.CommonAffineSegmentPartition
import PoincareConjecture.Proofs.M76.Mathlib.UniformPolygonSimplicity

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_partitioned_polygon_of_endpoint_loop {f : ℝ → E}
    (hf : FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1))
    (hfib : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      f x = f y ↔ x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)) :
    ∃ (n : ℕ) (t : Fin (n + 2) → ℝ) (Q : Polygon E (n + 1)),
      3 ≤ n + 1 ∧ StrictMono t ∧ t 0 = 0 ∧ t (Fin.last (n + 1)) = 1 ∧
      Function.Injective Q ∧ Q.HasSimplicialEdges ∧
      Q.boundary ℝ = f '' Icc (0 : ℝ) 1 ∧
      (∀ j, Q j = f (t j.castSucc)) ∧
      ∀ j, Q.edgeSet ℝ j = f '' Icc (t j.castSucc) (t j.succ) := by
  classical
  obtain ⟨B, hB, hB0, hB1, hformula⟩ := hf.exists_interval_breakpoints zero_le_one
  let T := B ∪ ({(1 : ℝ) / 3, 2 / 3} : Finset ℝ)
  have hBT : (B : Set ℝ) ⊆ T := fun x hx => Finset.mem_union_left _ hx
  have hT : (T : Set ℝ) ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hB hx
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> norm_num
  obtain ⟨n, t, ht, ht0, ht1, hrange, hgap⟩ := T.exists_ordered_partition
    zero_lt_one hT (hBT hB0) (hBT hB1)
  have hmem (j : Fin (n + 2)) : t j ∈ Icc (0 : ℝ) 1 := hT (hrange ▸ mem_range_self j)
  have hsize : 3 ≤ n + 1 := by
    obtain ⟨j, hj⟩ := hrange.symm ▸ (show (1 : ℝ) / 3 ∈ (T : Set ℝ) by simp [T])
    obtain ⟨k, hk⟩ := hrange.symm ▸ (show (2 : ℝ) / 3 ∈ (T : Set ℝ) by simp [T])
    have h0j : (0 : Fin (n + 2)) < j := ht.lt_iff_lt.mp (by rw [ht0, hj]; norm_num)
    have hjk : j < k := ht.lt_iff_lt.mp (by rw [hj, hk]; norm_num)
    have hkl : k < Fin.last (n + 1) := ht.lt_iff_lt.mp (by rw [ht1, hk]; norm_num)
    change 0 < j.val at h0j
    change j.val < k.val at hjk
    change k.val < n + 1 at hkl
    omega
  let Q : Polygon E (n + 1) := ⟨fun j => f (t j.castSucc)⟩
  have hend : f 0 = f 1 := (hfib _ ⟨le_rfl, zero_le_one⟩ _ ⟨zero_le_one, le_rfl⟩).mpr
    (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have hrotate (j : Fin (n + 1)) : Q (finRotate _ j) = f (t j.succ) := by
    refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [finRotate_last]
      change f (t 0) = f (t (Fin.last (n + 1)))
      rw [ht0, ht1]
      exact hend
    · have hk : finRotate (n + 1) k.castSucc = k.succ := finRotate_of_lt k.isLt
      rw [hk]
      rfl
  have hQ (j : Fin (n + 1)) : Q j = f (t j.castSucc) := rfl
  have hedge (j : Fin (n + 1)) : Q.edgeSet ℝ j = f '' Icc (t j.castSucc) (t j.succ) := by
    obtain ⟨A, hA⟩ := hformula _ _ (hmem _).1 (hmem _).2
      (ht Fin.castSucc_lt_succ) ((hgap j).mono_right hBT)
    have hseg : A '' affineSegment ℝ (t j.castSucc) (t j.succ) =
        affineSegment ℝ (A (t j.castSucc)) (A (t j.succ)) :=
      affineSegment_image A.toAffineMap _ _
    rw [Polygon.edgeSet, hQ, hrotate, hA (left_mem_Icc.mpr (ht Fin.castSucc_lt_succ).le),
      hA (right_mem_Icc.mpr (ht Fin.castSucc_lt_succ).le), ← hseg,
      affineSegment_eq_segment, segment_eq_Icc (ht Fin.castSucc_lt_succ).le]
    exact hA.image_eq.symm
  have hQi : Function.Injective Q := by
    intro j k hjk
    rcases (hfib _ (hmem _) _ (hmem _)).mp hjk with heq | ⟨_, hk⟩ | ⟨hj, _⟩
    · exact Fin.castSucc_injective _ (ht.injective heq)
    · have hlt := ht (show k.castSucc < Fin.last (n + 1) from k.isLt)
      rw [ht1, hk] at hlt
      exact (lt_irrefl _ hlt).elim
    · have hlt := ht (show j.castSucc < Fin.last (n + 1) from j.isLt)
      rw [ht1, hj] at hlt
      exact (lt_irrefl _ hlt).elim
  have hwhole (j : Fin (n + 1)) {r : ℝ}
      (hr : r ∈ Icc (t j.castSucc) (t j.succ)) : r ∈ Icc (0 : ℝ) 1 :=
    ⟨(hmem _).1.trans hr.1, hr.2.trans (hmem _).2⟩
  have hvertex (j : Fin (n + 1)) {r : ℝ}
      (hr : r = t j.castSucc ∨ r = t j.succ) : f r ∈ (Q.edgeVertices j : Set E) := by
    rcases hr with rfl | rfl
    · exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _)
    · rw [← hrotate]
      exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hextreme (j : Fin (n + 1)) {r : ℝ}
      (hr : r ∈ Icc (t j.castSucc) (t j.succ)) (he : r = 0 ∨ r = 1) :
      r = t j.castSucc ∨ r = t j.succ := by
    rcases he with rfl | rfl
    · exact Or.inl (le_antisymm (hmem _).1 hr.1)
    · exact Or.inr (le_antisymm hr.2 (hmem _).2)
  have hQs : Q.HasSimplicialEdges := by
    intro j k x hx
    by_cases hjk : j = k
    · subst k
      rw [inter_self, ← Q.edgeSet_eq_convexHull]
      exact hx.1
    · obtain ⟨r, hr, hrx⟩ := (hedge j).subset hx.1
      obtain ⟨s, hs, hsx⟩ := (hedge k).subset hx.2
      apply subset_convexHull ℝ _
      rcases (hfib _ (hwhole j hr) _ (hwhole k hs)).mp (hrx.trans hsx.symm) with
        hrs | ⟨hr0, hs1⟩ | ⟨hr1, hs0⟩
      · subst s
        obtain ⟨hj, hk⟩ := ht.eq_endpoints_of_mem_consecutive_Icc hjk hr hs
        exact ⟨hrx ▸ hvertex j hj, hsx ▸ hvertex k hk⟩
      · exact ⟨hrx ▸ hvertex j (hextreme j hr (Or.inl hr0)),
          hsx ▸ hvertex k (hextreme k hs (Or.inr hs1))⟩
      · exact ⟨hrx ▸ hvertex j (hextreme j hr (Or.inr hr1)),
          hsx ▸ hvertex k (hextreme k hs (Or.inl hs0))⟩
  have hQb : Q.boundary ℝ = f '' Icc (0 : ℝ) 1 := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      obtain ⟨r, hr, rfl⟩ := (hedge j).subset hj
      exact ⟨r, hwhole j hr, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨j, hj⟩ := ht.monotone.exists_mem_consecutive_Icc
        (show r ∈ Icc (t 0) (t (Fin.last (n + 1))) by rwa [ht0, ht1])
      exact mem_iUnion.mpr ⟨j, (hedge j).symm.subset ⟨r, hj, rfl⟩⟩
  exact ⟨n, t, Q, hsize, ht, ht0, ht1, hQi, hQs, hQb, hQ, hedge⟩

theorem exists_polygon_of_endpoint_loop {f : ℝ → E}
    (hf : FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1))
    (hfib : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      f x = f y ↔ x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)) :
    ∃ (N : ℕ) (Q : Polygon E (N + 3)), Function.Injective Q ∧
      Q.HasSimplicialEdges ∧ Q.boundary ℝ = f '' Icc (0 : ℝ) 1 := by
  obtain ⟨n, _, Q, hsize, _, _, _, hQi, hQs, hQb, _, _⟩ :=
    exists_partitioned_polygon_of_endpoint_loop hf hfib
  refine ⟨n + 1 - 3, ?_⟩
  rw [Nat.sub_add_cancel hsize]
  exact ⟨Q, hQi, hQs, hQb⟩

end PoincareConjecture.M76.Dehn
