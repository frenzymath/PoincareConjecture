import PoincareConjecture.Proofs.M25.Topology3D.Plane.UnitTriangle

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M25.Topology3D

theorem exists_openSegment_mem_interior_unitTriangle {z a : ℝ × ℝ}
    (hzpos : 0 < z.1 ∧ 0 < z.2) (hzH : z.1 + z.2 ≤ 1) (haH : a.1 + a.2 < 1) :
    ∃ w ∈ openSegment ℝ z a, w ∈ interior unitTriangle := by
  let g : ℝ → ℝ × ℝ := AffineMap.lineMap z a
  have hg : Continuous g := AffineMap.lineMap_continuous
  have hU : IsOpen {t : ℝ | 0 < (g t).1 ∧ 0 < (g t).2} :=
    (isOpen_lt continuous_const hg.fst).inter (isOpen_lt continuous_const hg.snd)
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU 0
    (by simpa only [mem_ofPred_eq, g, AffineMap.lineMap_apply_zero] using hzpos)
  let t := min ε 1 / 2
  have htpos : 0 < t := div_pos (lt_min hε zero_lt_one) (by norm_num)
  have ht1 : t < 1 := by dsimp [t]; linarith [min_le_right ε 1]
  have htε : t < ε := by dsimp [t]; linarith [min_le_left ε 1]
  have hwpos : 0 < (g t).1 ∧ 0 < (g t).2 :=
    hεU (by simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos] using htε)
  have hheight : (g t).1 + (g t).2 = (1 - t) * (z.1 + z.2) + t * (a.1 + a.2) := by
    simp only [g, AffineMap.lineMap_apply_module, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  refine ⟨g t, lineMap_mem_openSegment ℝ z a ⟨htpos, ht1⟩, ?_⟩
  rw [interior_unitTriangle]
  refine ⟨hwpos.1, hwpos.2, ?_⟩
  rw [hheight]
  nlinarith [mul_nonneg (sub_nonneg.mpr ht1.le) (sub_nonneg.mpr hzH),
    mul_pos htpos (sub_pos.mpr haH)]

theorem sum_eq_one_of_openSegment_base_hit {a b z : ℝ × ℝ}
    (hz : z ∈ openSegment ℝ a b) (hzpos : 0 < z.1 ∧ 0 < z.2)
    (hzH : z.1 + z.2 = 1) (hdis : Disjoint (segment ℝ a b) (interior unitTriangle)) :
    a.1 + a.2 = 1 ∧ b.1 + b.2 = 1 := by
  have hzseg : z ∈ segment ℝ a b := openSegment_subset_segment ℝ a b hz
  have hge (c : ℝ × ℝ) (hc : c ∈ segment ℝ a b) : 1 ≤ c.1 + c.2 := by
    by_contra! h
    obtain ⟨w, hw, hwT⟩ := exists_openSegment_mem_interior_unitTriangle hzpos hzH.le h
    exact Set.disjoint_left.mp hdis
      ((convex_segment (𝕜 := ℝ) a b).openSegment_subset hzseg hc hw) hwT
  have ha := hge a (left_mem_segment ℝ a b)
  have hb := hge b (right_mem_segment ℝ a b)
  rw [openSegment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have hheight : (1 - t) * (a.1 + a.2) + t * (b.1 + b.2) = 1 := by
    simpa only [AffineMap.lineMap_apply_module, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_add, add_add_add_comm] using hzH
  have ha0 : 0 ≤ (1 - t) * (a.1 + a.2 - 1) :=
    mul_nonneg (sub_nonneg.mpr ht.2.le) (sub_nonneg.mpr ha)
  have hb0 : 0 ≤ t * (b.1 + b.2 - 1) := mul_nonneg ht.1.le (sub_nonneg.mpr hb)
  have hsum : (1 - t) * (a.1 + a.2 - 1) + t * (b.1 + b.2 - 1) = 0 := by
    nlinarith [hheight]
  obtain ⟨haeq, hbeq⟩ := (add_eq_zero_iff_of_nonneg ha0 hb0).mp hsum
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp haeq).resolve_left (ne_of_gt (sub_pos.mpr ht.2))),
    sub_eq_zero.mp ((mul_eq_zero.mp hbeq).resolve_left ht.1.ne')⟩

theorem unit_base_endpoints_of_segment_base_hit {a b z : ℝ × ℝ}
    (hz : z ∈ segment ℝ a b) (hzpos : 0 < z.1 ∧ 0 < z.2) (hzH : z.1 + z.2 = 1)
    (hdis : Disjoint (segment ℝ a b) (interior unitTriangle))
    (hend : ∀ c ∈ ({a, b} : Set (ℝ × ℝ)), c ∈ unitTriangle →
      c ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)))
    (hinc : segment ℝ a b ∩ {(1, 0), (0, 1)} ⊆ {a, b}) :
    (a = (1, 0) ∧ b = (0, 1)) ∨ (a = (0, 1) ∧ b = (1, 0)) := by
  have hzT : z ∈ unitTriangle := ⟨hzpos.1.le, hzpos.2.le, hzH.le⟩
  have hznot : z ∉ ({a, b} : Set (ℝ × ℝ)) := by
    intro h
    rcases hend z h hzT with h | h
    · rw [h] at hzpos
      exact (lt_irrefl 0) hzpos.2
    · rw [h] at hzpos
      exact (lt_irrefl 0) hzpos.1
  have hza : a ≠ z := fun h => hznot (Or.inl h.symm)
  have hzb : b ≠ z := fun h => hznot (Or.inr h.symm)
  obtain ⟨haH, hbH⟩ := sum_eq_one_of_openSegment_base_hit
    (mem_openSegment_of_ne_left_right hza hzb hz) hzpos hzH hdis
  have hedgeH (w : ℝ × ℝ) (hw : w ∈ segment ℝ a b) : w.1 + w.2 = 1 := by
    have hconv : Convex ℝ {v : ℝ × ℝ | v.1 + v.2 = 1} :=
      (convex_singleton (𝕜 := ℝ) (1 : ℝ)).linear_preimage
        (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ)
    exact hconv.segment_subset haH hbH hw
  have hnomid (c : ℝ × ℝ) (hc : c ∈ ({a, b} : Set (ℝ × ℝ))) :
      ¬ (0 < c.1 ∧ c.1 < 1) := by
    intro h
    have hcH : c.1 + c.2 = 1 := by
      rcases hc with hc | hc
      · exact hc ▸ haH
      · exact hc ▸ hbH
    have hcT : c ∈ unitTriangle := ⟨h.1.le, by linarith, hcH.le⟩
    rcases hend c hc hcT with heq | heq
    · rw [heq] at h
      exact (lt_irrefl 1) h.2
    · rw [heq] at h
      exact (lt_irrefl 0) h.1
  have hproj : Prod.fst '' segment ℝ a b = Icc (min a.1 b.1) (max a.1 b.1) := by
    calc
      _ = segment ℝ a.1 b.1 := image_segment ℝ (LinearMap.fst ℝ ℝ ℝ).toAffineMap a b
      _ = _ := segment_eq_Icc' _ _
  have hzcoord : z.1 ∈ Icc (min a.1 b.1) (max a.1 b.1) :=
    hproj ▸ mem_image_of_mem Prod.fst hz
  have hz1 : z.1 < 1 := by linarith [hzpos.2]
  have hmin : min a.1 b.1 ≤ 0 := by
    by_contra! h
    rcases le_total a.1 b.1 with hab | hba
    · rw [min_eq_left hab] at h hzcoord
      exact hnomid a (Or.inl rfl) ⟨h, hzcoord.1.trans_lt hz1⟩
    · rw [min_eq_right hba] at h hzcoord
      exact hnomid b (Or.inr rfl) ⟨h, hzcoord.1.trans_lt hz1⟩
  have hmax : 1 ≤ max a.1 b.1 := by
    by_contra! h
    rcases le_total a.1 b.1 with hab | hba
    · rw [max_eq_right hab] at h hzcoord
      exact hnomid b (Or.inr rfl) ⟨hzpos.1.trans_le hzcoord.2, h⟩
    · rw [max_eq_left hba] at h hzcoord
      exact hnomid a (Or.inl rfl) ⟨hzpos.1.trans_le hzcoord.2, h⟩
  have hbase (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : (u, 1 - u) ∈ segment ℝ a b := by
    have huim : u ∈ Prod.fst '' segment ℝ a b :=
      hproj.symm ▸ ⟨hmin.trans hu.1, hu.2.trans hmax⟩
    obtain ⟨w, hw, hwu⟩ := huim
    have hwH := hedgeH w hw
    have heq : w = (u, 1 - u) := Prod.ext hwu (by linarith)
    exact heq ▸ hw
  have hA : (1, 0) ∈ ({a, b} : Set (ℝ × ℝ)) :=
    hinc ⟨by simpa using hbase 1 ⟨zero_le_one, le_rfl⟩, Or.inl rfl⟩
  have hB : (0, 1) ∈ ({a, b} : Set (ℝ × ℝ)) :=
    hinc ⟨by simpa using hbase 0 ⟨le_rfl, zero_le_one⟩, Or.inr rfl⟩
  simp only [mem_insert_iff, mem_singleton_iff] at hA hB
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · have h := hA.trans hB.symm
    norm_num at h
  · exact Or.inl ⟨hA.symm, hB.symm⟩
  · exact Or.inr ⟨hB.symm, hA.symm⟩
  · have h := hA.trans hB.symm
    norm_num at h

end PoincareConjecture.M25.Topology3D
