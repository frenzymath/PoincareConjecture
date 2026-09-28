import PoincareConjecture.Proofs.M76.Smoothing.CircleAngleCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.ShortCircleArc

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Smoothing

variable {n : ℕ} {theta : ℝ}

def circleGapArc (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    Set (AddCircle (2 * Real.pi)) :=
  (fun x : ℝ => (x : AddCircle (2 * Real.pi))) '' Icc (gapAngle w i) (gapAngle w i + w.val i)

def circleGapArcInterior (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    Set (AddCircle (2 * Real.pi)) :=
  (fun x : ℝ => (x : AddCircle (2 * Real.pi))) '' Ioo (gapAngle w i) (gapAngle w i + w.val i)

theorem gapAngle_add_le_fullTurn (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    gapAngle w i + w.val i ≤ 2 * Real.pi := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact (gapAngle_last_add w.val).trans w.property.2.1 |>.le
  · rw [← gapAngle_succ]
    exact (gapAngle_mem_Ico w.property j.succ).2.le

theorem gapAngle_add_le_of_lt (w : shortArcGapSpace n theta)
    {i j : Fin (n + 3)} (hij : i < j) : gapAngle w i + w.val i ≤ gapAngle w j := by
  have hi : i.val < n + 2 := by have := j.isLt; exact Nat.lt_of_lt_of_le hij (by omega)
  let k : Fin (n + 2) := ⟨i.val, hi⟩
  have hki : k.castSucc = i := Fin.ext rfl
  calc
    gapAngle w i + w.val i = gapAngle w k.succ := by rw [← hki, gapAngle_succ]
    _ ≤ gapAngle w j := (strictMono_gapAngle w.property).monotone (by
      change k.val + 1 ≤ j.val
      exact hij)

theorem exists_gapAngle_interval (w : shortArcGapSpace n theta) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (2 * Real.pi)) :
    ∃ i, x ∈ Icc (gapAngle w i) (gapAngle w i + w.val i) := by
  classical
  let s : Finset (Fin (n + 3)) := Finset.univ.filter (fun i => gapAngle w i ≤ x)
  have hs : s.Nonempty := ⟨0, by simp [s, hx.1]⟩
  let i := s.max' hs
  have himem : i ∈ s := Finset.max'_mem _ _
  refine ⟨i, (Finset.mem_filter.mp himem).2, ?_⟩
  by_cases hilast : i = Fin.last (n + 2)
  · rw [hilast, gapAngle_last_add, w.property.2.1]
    exact hx.2
  · have hi : i.val < n + 2 := by
      have hil := i.isLt
      have hine : i.val ≠ n + 2 := fun h => hilast (Fin.ext h)
      omega
    let j : Fin (n + 2) := ⟨i.val, hi⟩
    have hji : j.castSucc = i := Fin.ext rfl
    have hnot : j.succ ∉ s := by
      intro hmem
      have hle : j.succ ≤ i := Finset.le_max' _ _ hmem
      change j.val + 1 ≤ i.val at hle
      dsimp [j] at hle
      omega
    have hxj : x < gapAngle w j.succ := by
      apply lt_of_not_ge
      intro hle
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩)
    rw [gapAngle_succ, hji] at hxj
    exact hxj.le

theorem iUnion_circleGapArc (w : shortArcGapSpace n theta) :
    ⋃ i, circleGapArc w i = univ := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  apply eq_univ_iff_forall.mpr
  intro z
  obtain ⟨x, hx, hxz⟩ := AddCircle.eq_coe_Ico z
  obtain ⟨i, hi⟩ := exists_gapAngle_interval w (Ico_subset_Icc_self hx)
  exact mem_iUnion.mpr ⟨i, ⟨x, hi, hxz⟩⟩

theorem pairwise_disjoint_circleGapArcInterior (w : shortArcGapSpace n theta) :
    Pairwise (fun i j => Disjoint (circleGapArcInterior w i) (circleGapArcInterior w j)) := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  intro i j hij
  apply disjoint_left.mpr
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  have hxrange : x ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
    ⟨(gapAngle_mem_Ico w.property i).1.trans hx.1.le,
      by simpa using hx.2.trans_le (gapAngle_add_le_fullTurn w i)⟩
  have hyrange : y ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
    ⟨(gapAngle_mem_Ico w.property j).1.trans hy.1.le,
      by simpa using hy.2.trans_le (gapAngle_add_le_fullTurn w j)⟩
  have hxy : x = y :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico hxrange hyrange).mp (hxz.trans hyz.symm)
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hle := gapAngle_add_le_of_lt w hij
    linarith [hx.2, hy.1]
  · have hle := gapAngle_add_le_of_lt w hji
    linarith [hy.2, hx.1]

theorem isometry_circleGapArc (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    Isometry (fun x : Icc (gapAngle w i) (gapAngle w i + w.val i) =>
      (x.val : AddCircle (2 * Real.pi))) :=
  AddCircle.isometry_coe_shortInterval (by positivity) (by linarith [(w.property.1 i).2])

noncomputable def circleGapArcHomeomorph (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    Icc (gapAngle w i) (gapAngle w i + w.val i) ≃ₜ circleGapArc w i :=
  AddCircle.shortArcHomeomorph (by positivity) (by linarith [(w.property.1 i).2])

theorem circleGapArc_endpoint (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    ((gapAngle w i + w.val i : ℝ) : AddCircle (2 * Real.pi)) =
      circleGapVertices w (i + 1) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [gapAngle_last_add, w.property.2.1, Fin.last_add_one]
    simp [circleGapVertices, AddCircle.coe_period]
  · rw [Fin.coeSucc_eq_succ, ← gapAngle_succ]
    rfl

theorem circleGapVertex_notMem_arcInterior (w : shortArcGapSpace n theta)
    (i k : Fin (n + 3)) : circleGapVertices w k ∉ circleGapArcInterior w i := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  rintro ⟨x, hx, hxk⟩
  have hxrange : x ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
    ⟨(gapAngle_mem_Ico w.property i).1.trans hx.1.le,
      by simpa using hx.2.trans_le (gapAngle_add_le_fullTurn w i)⟩
  change (x : AddCircle (2 * Real.pi)) = (gapAngle w k : AddCircle (2 * Real.pi)) at hxk
  have hxreal : x = gapAngle w k :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico hxrange
      (by simpa using gapAngle_mem_Ico w.property k)).mp hxk
  rcases le_or_gt k i with hki | hik
  · have hle := (strictMono_gapAngle w.property).monotone hki
    linarith [hx.1]
  · have hle := gapAngle_add_le_of_lt w hik
    linarith [hx.2]

theorem circleGapArc_eq_interior_union_endpoints (w : shortArcGapSpace n theta)
    (i : Fin (n + 3)) : circleGapArc w i =
      circleGapArcInterior w i ∪ {circleGapVertices w i, circleGapVertices w (i + 1)} := by
  unfold circleGapArc circleGapArcInterior
  rw [← Ioo_union_both (show gapAngle w i ≤ gapAngle w i + w.val i by
    linarith [(w.property.1 i).1]), image_union, image_pair, circleGapArc_endpoint]
  rfl

theorem circleGapVertex_mem_arc_iff (w : shortArcGapSpace n theta)
    (i k : Fin (n + 3)) : circleGapVertices w k ∈ circleGapArc w i ↔ k = i ∨ k = i + 1 := by
  rw [circleGapArc_eq_interior_union_endpoints, mem_union,
    or_iff_right (circleGapVertex_notMem_arcInterior w i k)]
  simp only [mem_insert_iff, mem_singleton_iff, (injective_circleGapVertices w).eq_iff]

theorem circleGapArc_inter (w : shortArcGapSpace n theta) {i j : Fin (n + 3)} (hij : i ≠ j) :
    circleGapArc w i ∩ circleGapArc w j =
      {circleGapVertices w i, circleGapVertices w (i + 1)} ∩
        {circleGapVertices w j, circleGapVertices w (j + 1)} := by
  ext z
  rw [circleGapArc_eq_interior_union_endpoints, circleGapArc_eq_interior_union_endpoints]
  constructor
  · rintro ⟨hi, hj⟩
    have hnoti : z ∉ circleGapArcInterior w i := by
      intro hz
      rcases hj with hj | hj
      · exact (pairwise_disjoint_circleGapArcInterior w hij).le_bot ⟨hz, hj⟩
      · rcases hj with rfl | hj
        · exact circleGapVertex_notMem_arcInterior w i j hz
        · rw [mem_singleton_iff] at hj
          subst z
          exact circleGapVertex_notMem_arcInterior w i (j + 1) hz
    have hiends := hi.resolve_left hnoti
    refine ⟨hiends, hj.resolve_left ?_⟩
    intro hz
    rcases hiends with rfl | hiends
    · exact circleGapVertex_notMem_arcInterior w j i hz
    · rw [mem_singleton_iff] at hiends
      subst z
      exact circleGapVertex_notMem_arcInterior w j (i + 1) hz
  · rintro ⟨hi, hj⟩
    exact ⟨Or.inr hi, Or.inr hj⟩

end PoincareConjecture.M76.Smoothing
