import PoincareConjecture.Proofs.M25.Topology3D.Polygon.DeleteVertex
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.PushIn
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.Admissible
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.SimpleTriangle
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition










set_option autoImplicit false

open Set Function
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

section Determinant

variable {W : Type*} [AddCommGroup W] [Module ℝ W]



noncomputable def triangleEdgeDet (b : AffineBasis (Fin 3) ℝ W) (x y : W) : ℝ :=
  (b.coord 1 x - 1 / 3) * (b.coord 2 y - 1 / 3) -
    (b.coord 2 x - 1 / 3) * (b.coord 1 y - 1 / 3)



theorem triangleEdgeDet_midpoint_right (b : AffineBasis (Fin 3) ℝ W) (x y : W) :
    triangleEdgeDet b x (midpoint ℝ x y) = triangleEdgeDet b x y / 2 := by
  simp only [triangleEdgeDet, AffineMap.map_midpoint]
  simp only [midpoint_eq_smul_add, smul_eq_mul, invOf_eq_inv]
  ring



theorem triangleEdgeDet_midpoint_left (b : AffineBasis (Fin 3) ℝ W) (x y : W) :
    triangleEdgeDet b (midpoint ℝ x y) y = triangleEdgeDet b x y / 2 := by
  simp only [triangleEdgeDet, AffineMap.map_midpoint]
  simp only [midpoint_eq_smul_add, smul_eq_mul, invOf_eq_inv]
  ring

end Determinant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem polygon_ext_of_apply (p q : Polygon E n) (h : ∀ i, p i = q i) : p = q := by
  cases p
  cases q
  congr
  exact funext h



noncomputable def polygonClosingMidpoint (q : Polygon E (n + 3)) : Polygon E (n + 4) :=
  ⟨Fin.snoc q (midpoint ℝ (q (Fin.last (n + 2))) (q 0))⟩

private theorem closingMidpoint_edges (q : Polygon E (n + 3)) :
    (∀ i : Fin (n + 2), (polygonClosingMidpoint q).edgeSet ℝ i.castSucc.castSucc =
      q.edgeSet ℝ i.castSucc) ∧
    (polygonClosingMidpoint q).edgeSet ℝ (Fin.last (n + 2)).castSucc =
      segment ℝ (q (Fin.last (n + 2))) (midpoint ℝ (q (Fin.last (n + 2))) (q 0)) ∧
    (polygonClosingMidpoint q).edgeSet ℝ (Fin.last (n + 3)) =
      segment ℝ (midpoint ℝ (q (Fin.last (n + 2))) (q 0)) (q 0) := by
  have hval (i : Fin (n + 3)) : polygonClosingMidpoint q i.castSucc = q i := by
    simp only [polygonClosingMidpoint, Fin.snoc_castSucc]
  have hlast : polygonClosingMidpoint q (Fin.last (n + 3)) =
      midpoint ℝ (q (Fin.last (n + 2))) (q 0) := by
    simp only [polygonClosingMidpoint, Fin.snoc_last]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [polygon_edgeSet_eq_segment, polygon_edgeSet_eq_segment,
      show finRotate (n + 4) i.castSucc.castSucc = i.succ.castSucc from
        finRotate_of_lt (show i.val < n + 3 by omega),
      show finRotate (n + 3) i.castSucc = i.succ from finRotate_of_lt i.isLt]
    rw [hval, hval]
  · rw [polygon_edgeSet_eq_segment,
      show finRotate (n + 4) (Fin.last (n + 2)).castSucc = Fin.last (n + 3) from
        finRotate_of_lt (show n + 2 < n + 3 by omega)]
    rw [hval, hlast]
  · rw [polygon_edgeSet_eq_segment, finRotate_last, hlast]
    exact congrArg (segment ℝ _) (hval 0)



theorem polygonClosingMidpoint_boundary (q : Polygon E (n + 3)) :
    (polygonClosingMidpoint q).boundary ℝ = q.boundary ℝ := by
  let a := q (Fin.last (n + 2))
  let b := q 0
  let m := midpoint ℝ a b
  have hs : segment ℝ a m ∪ segment ℝ m b = segment ℝ a b := by
    have h := (segment_split_at_point (midpoint_mem_segment (𝕜 := ℝ) a b)).1
    change segment ℝ m a ∪ segment ℝ m b = segment ℝ a b at h
    rwa [segment_symm ℝ m a] at h
  have hedge : q.edgeSet ℝ (Fin.last (n + 2)) = segment ℝ a b := by
    rw [polygon_edgeSet_eq_segment, finRotate_last]
  obtain ⟨he, hl, hr⟩ := closingMidpoint_edges q
  apply subset_antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff _ x).mp hx
    revert hi
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro hi
      rw [hr] at hi
      apply polygon_edgeSet_subset_boundary q (Fin.last (n + 2))
      rw [hedge, ← hs]
      exact Or.inr hi
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · intro hi
        rw [hl] at hi
        apply polygon_edgeSet_subset_boundary q (Fin.last (n + 2))
        rw [hedge, ← hs]
        exact Or.inl hi
      · intro hi
        rw [he] at hi
        exact polygon_edgeSet_subset_boundary q _ hi
  · intro x hx
    obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff q x).mp hx
    revert hi
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro hi
      rw [hedge, ← hs] at hi
      rcases hi with hi | hi
      · exact polygon_edgeSet_subset_boundary _ _ (hl.symm ▸ hi)
      · exact polygon_edgeSet_subset_boundary _ _ (hr.symm ▸ hi)
    · intro hi
      exact polygon_edgeSet_subset_boundary _ _ ((he j).symm ▸ hi)



theorem IsSimplePolygon.isSimple_polygonClosingMidpoint {q : Polygon E (n + 3)}
    (hq : IsSimplePolygon q) : IsSimplePolygon (polygonClosingMidpoint q) := by
  let a := q (Fin.last (n + 2))
  let b := q 0
  let m := midpoint ℝ a b
  let r := polygonClosingMidpoint q
  have hab : a ≠ b := by
    simpa only [a, b, finRotate_last] using hq.hasNondegenerateEdges (Fin.last (n + 2))
  have hma : m ≠ a := fun h => hab ((midpoint_eq_left_iff (R := ℝ)).mp h)
  have hmb : m ≠ b := fun h => hab ((midpoint_eq_right_iff (R := ℝ)).mp h)
  have hm : m ∈ segment ℝ a b := midpoint_mem_segment (𝕜 := ℝ) a b
  have hs := segment_split_at_point hm
  rw [segment_symm ℝ m a] at hs
  have hbnot : b ∉ segment ℝ a m := by
    intro h
    have hx : b ∈ ({m} : Set E) := hs.2 ▸ ⟨h, right_mem_segment ℝ m b⟩
    exact hmb (show b = m from hx).symm
  have hanot : a ∉ segment ℝ m b := by
    intro h
    have hx : a ∈ ({m} : Set E) := hs.2 ▸ ⟨left_mem_segment ℝ a m, h⟩
    exact hma (show a = m from hx).symm
  have hclose : q.edgeSet ℝ (Fin.last (n + 2)) = segment ℝ a b := by
    rw [polygon_edgeSet_eq_segment, finRotate_last]
  have hmi (i : Fin (n + 3)) : q i ≠ m := by
    intro heq
    have hi : q i ∈ q.edgeSet ℝ (Fin.last (n + 2)) := by rwa [heq, hclose]
    rcases (hq.vertex_mem_edgeSet_iff i _).mp hi with hi | hi
    · exact hma (heq.symm.trans (congrArg q hi))
    · rw [finRotate_last] at hi
      exact hmb (heq.symm.trans (congrArg q hi))
  have hval (i : Fin (n + 3)) : r i.castSucc = q i := by
    simp only [r, polygonClosingMidpoint, Fin.snoc_castSucc]
  have hlast : r (Fin.last (n + 3)) = m := by
    simp only [r, polygonClosingMidpoint, Fin.snoc_last, m, a, b]
  obtain ⟨he, hl, hr⟩ := closingMidpoint_edges q
  have hlinc (i : Fin (n + 2)) :
      segment ℝ a m ∩ q.edgeSet ℝ i.castSucc ⊆
        {a, m} ∩ {q i.castSucc, q (finRotate (n + 3) i.castSucc)} := by
    rintro x ⟨hx, hi⟩
    have hxq : x ∈ q.edgeSet ℝ (Fin.last (n + 2)) := by
      rw [hclose, ← hs.1]
      exact Or.inl hx
    have hh := hq.edges_inter (Fin.last (n + 2)) i.castSucc
      (Fin.castSucc_ne_last i).symm ⟨hxq, hi⟩
    rw [finRotate_last] at hh
    rcases hh.1 with ha | hb
    · exact ⟨Or.inl ha, hh.2⟩
    · have hxb : x = b := hb
      exact False.elim (hbnot (hxb ▸ hx))
  have hrinc (i : Fin (n + 2)) :
      segment ℝ m b ∩ q.edgeSet ℝ i.castSucc ⊆
        {m, b} ∩ {q i.castSucc, q (finRotate (n + 3) i.castSucc)} := by
    rintro x ⟨hx, hi⟩
    have hxq : x ∈ q.edgeSet ℝ (Fin.last (n + 2)) := by
      rw [hclose, ← hs.1]
      exact Or.inr hx
    have hh := hq.edges_inter (Fin.last (n + 2)) i.castSucc
      (Fin.castSucc_ne_last i).symm ⟨hxq, hi⟩
    rw [finRotate_last] at hh
    rcases hh.1 with ha | hb
    · have hxa : x = a := ha
      exact False.elim (hanot (hxa ▸ hx))
    · exact ⟨Or.inr hb, hh.2⟩
  have hends (i : Fin (n + 2)) :
      r (finRotate (n + 4) i.castSucc.castSucc) = q (finRotate (n + 3) i.castSucc) := by
    rw [show finRotate (n + 4) i.castSucc.castSucc = i.succ.castSucc from
        finRotate_of_lt (show i.val < n + 3 by omega),
      show finRotate (n + 3) i.castSucc = i.succ from finRotate_of_lt i.isLt]
    exact hval i.succ
  have hlend : r (finRotate (n + 4) (Fin.last (n + 2)).castSucc) = m := by
    rw [show finRotate (n + 4) (Fin.last (n + 2)).castSucc = Fin.last (n + 3) from
      finRotate_of_lt (show n + 2 < n + 3 by omega)]
    exact hlast
  have hrend : r (finRotate (n + 4) (Fin.last (n + 3))) = b := by
    rw [finRotate_last]
    exact hval 0
  have hleftRight : r.edgeSet ℝ (Fin.last (n + 2)).castSucc ∩
      r.edgeSet ℝ (Fin.last (n + 3)) ⊆ {m} := by
    rw [hl, hr]
    exact hs.2.le
  have hnot : m ∉ range q := by
    rintro ⟨i, hi⟩
    exact hmi i hi
  refine ⟨by omega, Fin.snoc_injective_of_injective hq.vertices_injective hnot, ?_⟩
  intro i j hij
  have hcheck : ∀ i j : Fin (n + 4), i < j →
      r.edgeSet ℝ i ∩ r.edgeSet ℝ j ⊆
        {r i, r (finRotate (n + 4) i)} ∩ {r j, r (finRotate (n + 4) j)} := by
    intro i j hij
    by_cases hj : j = Fin.last (n + 3)
    · subst j
      have hi : i ≠ Fin.last (n + 3) := ne_of_lt hij
      obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      by_cases hi : i = Fin.last (n + 2)
      · subst i
        intro x hx
        have hx' : x = m := hleftRight hx
        rw [hx', hval, hlend, hlast, hrend]
        exact ⟨Or.inr rfl, Or.inl rfl⟩
      · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        intro x hx
        rw [he, hr] at hx
        have hh := hrinc i ⟨hx.2, hx.1⟩
        rw [hval, hends, hlast, hrend]
        exact ⟨hh.2, hh.1⟩
    · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
      have hi : i ≠ Fin.last (n + 3) := by
        intro h
        subst i
        exact (not_lt_of_ge (Fin.le_last _)) hij
      obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      have hij' : i < j := hij
      by_cases hj : j = Fin.last (n + 2)
      · subst j
        obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (ne_of_lt hij')
        intro x hx
        rw [he, hl] at hx
        have hh := hlinc i ⟨hx.2, hx.1⟩
        rw [hval, hends, hval, hlend]
        exact ⟨hh.2, hh.1⟩
      · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
        have hi : i ≠ Fin.last (n + 2) := by
          intro h
          subst i
          exact (not_lt_of_ge (Fin.le_last _)) hij'
        obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        rw [he, he, hval, hval, hends, hends]
        exact hq.edges_inter _ _ (ne_of_lt hij')
  rcases lt_or_gt_of_ne hij with h | h
  · exact hcheck i j h
  · intro x hx
    have hh := hcheck j i h ⟨hx.2, hx.1⟩
    exact ⟨hh.2, hh.1⟩



theorem contDiff_polygonClosingMidpoint_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {k : ℕ∞ω} {q : V → Polygon E (n + 3)}
    (hq : ∀ i, ContDiff ℝ k (fun z => q z i)) (i : Fin (n + 4)) :
    ContDiff ℝ k (fun z => polygonClosingMidpoint (q z) i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [polygonClosingMidpoint, Fin.snoc_last, midpoint_eq_smul_add]
    exact contDiff_const.smul ((hq _).add (hq _))
  · simpa only [polygonClosingMidpoint, Fin.snoc_castSucc] using hq j



theorem polygonClosingMidpoint_det_pos (b : AffineBasis (Fin 3) ℝ E)
    (q : Polygon E (n + 3))
    (hq : ∀ i, 0 < triangleEdgeDet b (q i) (q (finRotate (n + 3) i))) :
    ∀ i, 0 < triangleEdgeDet b (polygonClosingMidpoint q i)
      (polygonClosingMidpoint q (finRotate (n + 4) i)) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [finRotate_last, polygonClosingMidpoint, Fin.snoc_last,
      Fin.snoc_apply_zero, triangleEdgeDet_midpoint_left]
    exact div_pos (by simpa only [finRotate_last] using hq (Fin.last (n + 2))) (by norm_num)
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [show finRotate (n + 4) (Fin.last (n + 2)).castSucc = Fin.last (n + 3) from
        finRotate_of_lt (show n + 2 < n + 3 by omega)]
      simp only [polygonClosingMidpoint, Fin.snoc_castSucc, Fin.snoc_last,
        triangleEdgeDet_midpoint_right]
      exact div_pos (by simpa only [finRotate_last] using hq (Fin.last (n + 2))) (by norm_num)
    · rw [show finRotate (n + 4) k.castSucc.castSucc = k.succ.castSucc from
        finRotate_of_lt (show k.val < n + 3 by omega)]
      simp only [polygonClosingMidpoint, Fin.snoc_castSucc]
      simpa only [show finRotate (n + 3) k.castSucc = k.succ from finRotate_of_lt k.isLt]
        using hq k.castSucc



def polygonCyclicRelabel (p : Polygon E n) (σ : Equiv.Perm (Fin n)) : Polygon E n :=
  ⟨fun i => p (σ i)⟩



theorem IsSimplePolygon.isSimple_polygonCyclicRelabel {p : Polygon E n}
    (hp : IsSimplePolygon p) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, σ (finRotate n i) = finRotate n (σ i)) :
    IsSimplePolygon (polygonCyclicRelabel p σ) := by
  refine ⟨hp.three_le, hp.vertices_injective.comp σ.injective, ?_⟩
  intro i j hij
  have he (i : Fin n) : (polygonCyclicRelabel p σ).edgeSet ℝ i = p.edgeSet ℝ (σ i) := by
    simp only [polygon_edgeSet_eq_segment, polygonCyclicRelabel, hσ]
  rw [he, he]
  simpa only [polygonCyclicRelabel, hσ] using hp.edges_inter (σ i) (σ j)
    (fun h => hij (σ.injective h))



theorem polygonCyclicRelabel_boundary (p : Polygon E n) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, σ (finRotate n i) = finRotate n (σ i)) :
    (polygonCyclicRelabel p σ).boundary ℝ = p.boundary ℝ := by
  have he (i : Fin n) : (polygonCyclicRelabel p σ).edgeSet ℝ i = p.edgeSet ℝ (σ i) := by
    simp only [polygon_edgeSet_eq_segment, polygonCyclicRelabel, hσ]
  ext x
  simp only [polygon_mem_boundary_iff, he]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨σ i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨σ.symm i, by simpa only [σ.apply_symm_apply] using hi⟩



noncomputable def polygonRetainDeletedMidpoint (k : Fin (n + 4))
    (q : Polygon E (n + 3)) : Polygon E (n + 4) :=
  polygonCyclicRelabel (polygonClosingMidpoint q) (finCycle (finRotate (n + 4) k)).symm

private theorem midpointRelabel_commutes (k : Fin (n + 4)) :
    ∀ i, (finCycle (finRotate (n + 4) k)).symm (finRotate (n + 4) i) =
      finRotate (n + 4) ((finCycle (finRotate (n + 4) k)).symm i) := by
  intro i
  apply (finCycle (finRotate (n + 4) k)).injective
  simp only [Equiv.apply_symm_apply, finCycle_apply, finRotate_apply]
  simp only [finCycle_symm_apply]
  abel



theorem polygonRetainDeletedMidpoint_properties (k : Fin (n + 4))
    (q : Polygon E (n + 3)) :
    (IsSimplePolygon q → IsSimplePolygon (polygonRetainDeletedMidpoint k q)) ∧
    (polygonRetainDeletedMidpoint k q).boundary ℝ = q.boundary ℝ := by
  constructor
  · intro hq
    exact hq.isSimple_polygonClosingMidpoint.isSimple_polygonCyclicRelabel _
      (midpointRelabel_commutes k)
  · exact (polygonCyclicRelabel_boundary _ _ (midpointRelabel_commutes k)).trans
      (polygonClosingMidpoint_boundary q)



theorem polygonRetainDeletedMidpoint_det_pos (b : AffineBasis (Fin 3) ℝ E)
    (k : Fin (n + 4)) (q : Polygon E (n + 3))
    (hq : ∀ i, 0 < triangleEdgeDet b (q i) (q (finRotate (n + 3) i))) :
    ∀ i, 0 < triangleEdgeDet b (polygonRetainDeletedMidpoint k q i)
      (polygonRetainDeletedMidpoint k q (finRotate (n + 4) i)) := by
  intro i
  simp only [polygonRetainDeletedMidpoint, polygonCyclicRelabel, midpointRelabel_commutes]
  exact polygonClosingMidpoint_det_pos b q hq _



theorem polygonRetainDeletedMidpoint_delete (p : Polygon E (n + 4)) (k : Fin (n + 4))
    (hk : p k = midpoint ℝ (p ((finRotate (n + 4)).symm k)) (p (finRotate (n + 4) k))) :
    polygonRetainDeletedMidpoint k (polygonDeleteVertex p k) = p := by
  let σ := finCycle (finRotate (n + 4) k)
  have hσ (i : Fin (n + 4)) : σ (finRotate (n + 4) i) = finRotate (n + 4) (σ i) := by
    simp only [σ, finCycle_apply, finRotate_apply]
    ac_rfl
  have hlast : σ (Fin.last (n + 3)) = k := by
    apply (finRotate (n + 4)).injective
    rw [← hσ, finRotate_last]
    simp only [σ, finCycle_apply, zero_add]
  have hcast (j : Fin (n + 3)) :
      cyclicArcIndex (finRotate (n + 4) k) (n + 2) j = σ j.castSucc := by
    have h := (congrFun (finCycle_eq_finRotate_iterate
      (k := j.castSucc)) (finRotate (n + 4) k)).symm
    simpa only [cyclicArcIndex, σ, finCycle_apply, Fin.val_castSucc, add_comm] using h
  have hEq (j : Fin (n + 4)) :
      polygonClosingMidpoint (polygonDeleteVertex p k) j = p (σ j) := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [polygonClosingMidpoint, Fin.snoc_last, polygonDeleteVertex, polygonArc]
      rw [cyclicArcIndex_delete_last, cyclicArcIndex_zero, hlast]
      exact hk.symm
    · simp only [polygonClosingMidpoint, Fin.snoc_castSucc, polygonDeleteVertex,
        polygonArc, hcast]
  apply polygon_ext_of_apply
  intro i
  change polygonClosingMidpoint (polygonDeleteVertex p k) (σ.symm i) = p i
  rw [hEq, σ.apply_symm_apply]



theorem contDiff_polygonRetainDeletedMidpoint_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : ℕ∞ω} {q : V → Polygon E (n + 3)}
    (hq : ∀ i, ContDiff ℝ s (fun z => q z i)) (k i : Fin (n + 4)) :
    ContDiff ℝ s (fun z => polygonRetainDeletedMidpoint k (q z) i) :=
  contDiff_polygonClosingMidpoint_apply hq _




theorem IsSimplePolygon.exists_smooth_triangle_motion [FiniteDimensional ℝ E]
    {p : Polygon E n} (hp : IsSimplePolygon p) (hdim : Module.finrank ℝ E = 2) :
    ∃ P : ℝ → Polygon E n, (∀ i, ContDiff ℝ ∞ (fun t => P t i)) ∧
      P 0 = p ∧ (∀ t ∈ Icc (0 : ℝ) 1, IsSimplePolygon (P t)) ∧
      ∃ b : AffineBasis (Fin 3) ℝ E,
        (P 1).boundary ℝ = frontier (convexHull ℝ (range b)) ∧
        ∀ i, 0 < triangleEdgeDet b (P 1 i) (P 1 (finRotate n i)) := by
  have hmain : ∀ m : ℕ, ∀ p : Polygon E (m + 3), IsSimplePolygon p →
      ∃ P : ℝ → Polygon E (m + 3), (∀ i, ContDiff ℝ ∞ (fun t => P t i)) ∧
        P 0 = p ∧ (∀ t ∈ Icc (0 : ℝ) 1, IsSimplePolygon (P t)) ∧
        ∃ b : AffineBasis (Fin 3) ℝ E,
          (P 1).boundary ℝ = frontier (convexHull ℝ (range b)) ∧
          ∀ i, 0 < triangleEdgeDet b (P 1 i) (P 1 (finRotate (m + 3) i)) := by
    intro m
    induction m with
    | zero =>
      intro p hp
      refine ⟨fun _ => p, fun _ => contDiff_const, rfl, fun _ _ => hp,
        hp.triangleAffineBasis hdim, hp.triangle_boundary_eq_frontier hdim, ?_⟩
      intro i
      change 0 < triangleEdgeDet (hp.triangleAffineBasis hdim)
        ((hp.triangleAffineBasis hdim) i) ((hp.triangleAffineBasis hdim) (finRotate 3 i))
      fin_cases i <;>
        norm_num [triangleEdgeDet, AffineBasis.coord_apply, finRotate_apply, Fin.ext_iff,
          Fin.val_add_eq_ite]
    | succ m ih =>
      intro p hp
      obtain ⟨k, _, _, had, _⟩ := hp.exists_admissible_vertex_away_edge hdim (by omega) 0
      let p1 := polygonPushVertex p k 1
      have hp1 : IsSimplePolygon p1 := hp.isSimple_polygonPushVertex k had ⟨zero_le_one, le_rfl⟩
      have hpk : (finRotate (m + 4)).symm k ≠ k := by
        intro h
        have hh := congrArg (finRotate (m + 4)) h
        rw [Equiv.apply_symm_apply] at hh
        exact hp.hasNondegenerateEdges k (congrArg p hh)
      have hnk : finRotate (m + 4) k ≠ k :=
        fun h => hp.hasNondegenerateEdges k (congrArg p h.symm)
      have hp1other (i : Fin (m + 4)) (hi : i ≠ k) : p1 i = p i :=
        polygonReplaceVertex_apply_of_ne p k _ hi
      have hmid : p1 k = midpoint ℝ (p1 ((finRotate (m + 4)).symm k))
          (p1 (finRotate (m + 4) k)) := by
        rw [hp1other _ hpk, hp1other _ hnk]
        exact polygonPushVertex_one_vertex p k
      have hstraight : p1 k ∈ segment ℝ (p1 ((finRotate (m + 4)).symm k))
          (p1 (finRotate (m + 4) k)) := by
        rw [hmid]
        exact midpoint_mem_segment _ _
      let q := polygonDeleteVertex p1 k
      obtain ⟨Q, hQ, hQ0, hQs, b, hQ1, hQpos⟩ :=
        ih q (hp1.isSimple_polygonDeleteVertex k hstraight)
      have hrestore : polygonRetainDeletedMidpoint k (Q 0) = p1 := by
        rw [hQ0]
        exact polygonRetainDeletedMidpoint_delete p1 k hmid
      let u : ℝ → ℝ := fun t => Real.smoothTransition (3 * t)
      let v : ℝ → ℝ := fun t => Real.smoothTransition (3 * t - 2)
      have hu : ContDiff ℝ ∞ u :=
        Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)
      have hv : ContDiff ℝ ∞ v :=
        Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
      let U : ℝ → Polygon E (m + 4) := fun t => polygonPushVertex p k (u t)
      let V : ℝ → Polygon E (m + 4) := fun t => polygonRetainDeletedMidpoint k (Q (v t))
      let P : ℝ → Polygon E (m + 4) := fun t => ⟨fun i => U t i + V t i - p1 i⟩
      have hU (i : Fin (m + 4)) : ContDiff ℝ ∞ (fun t => U t i) :=
        contDiff_polygonPushVertex_apply k i (fun _ => contDiff_const) hu
      have hV (i : Fin (m + 4)) : ContDiff ℝ ∞ (fun t => V t i) :=
        contDiff_polygonRetainDeletedMidpoint_apply (fun j => (hQ j).comp hv) k i
      have hPleft (t : ℝ) (ht : t ≤ 1 / 2) : P t = U t := by
        have hvt : v t = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
        apply polygon_ext_of_apply
        intro i
        change U t i + polygonRetainDeletedMidpoint k (Q (v t)) i - p1 i = U t i
        rw [hvt, hrestore, add_sub_cancel_right]
      have hPright (t : ℝ) (ht : 1 / 2 ≤ t) : P t = V t := by
        have hut : u t = 1 := Real.smoothTransition.one_of_one_le (by linarith)
        apply polygon_ext_of_apply
        intro i
        change polygonPushVertex p k (u t) i + V t i - p1 i = V t i
        rw [hut]
        change p1 i + V t i - p1 i = V t i
        abel
      refine ⟨P, fun i => ((hU i).add (hV i)).sub contDiff_const, ?_, ?_, b, ?_⟩
      · rw [hPleft 0 (by norm_num)]
        change polygonPushVertex p k (Real.smoothTransition (3 * 0)) = p
        rw [mul_zero, Real.smoothTransition.zero, polygonPushVertex_zero]
      · intro t _
        rcases le_total t (1 / 2) with ht | ht
        · rw [hPleft t ht]
          exact hp.isSimple_polygonPushVertex k had
            ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
        · rw [hPright t ht]
          exact (polygonRetainDeletedMidpoint_properties k _).1
            (hQs _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)
      · have hP1 : P 1 = polygonRetainDeletedMidpoint k (Q 1) := by
          rw [hPright 1 (by norm_num)]
          change polygonRetainDeletedMidpoint k (Q (Real.smoothTransition (3 * 1 - 2))) = _
          rw [show (3 * (1 : ℝ) - 2) = 1 by norm_num, Real.smoothTransition.one]
        rw [hP1]
        exact ⟨((polygonRetainDeletedMidpoint_properties k _).2).trans hQ1,
          polygonRetainDeletedMidpoint_det_pos b k (Q 1) hQpos⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hp.three_le
  have hn : n = m + 3 := by omega
  clear hm
  subst n
  exact hmain m p hp

end PoincareConjecture.M25.Topology3D
