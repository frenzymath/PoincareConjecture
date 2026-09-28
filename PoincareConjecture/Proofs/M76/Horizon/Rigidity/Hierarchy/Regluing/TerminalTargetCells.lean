import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.TerminalCoordinatePL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Arcs.Mathlib.ShiftedCircleClosedArc










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "E3" => ((ℝ × ℝ) × ℝ)
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance : Fact (0 < p) := ⟨by norm_num⟩

def hamiltonZeroTerminalTargetCell (u v a b alpha beta : ℝ) : Set X0 :=
  (Q0) ⁻¹' ((AddCircle.closedIntervalArc p u v ×ˢ AddCircle.closedIntervalArc p a b) ×ˢ
    AddCircle.closedIntervalArc p alpha beta)

private theorem short_arc_frontier {l r : ℝ} (hlr : l ≤ r) (hwidth : r < l + p) :
    frontier (AddCircle.closedIntervalArc p l r) = {(l : C0), (r : C0)} :=
  AddCircle.frontier_closedIntervalArc_shifted p (c := (l + r - p) / 2)
    (by linarith) hlr (by linarith)

theorem hamiltonZero_terminal_target_cell_eq_projected_box (u v a b alpha beta : ℝ) :
    hamiltonZeroTerminalTargetCell u v a b alpha beta =
      (fun z : E3 => (Q0).symm (((z.1.1 : C0), (z.1.2 : C0)), (z.2 : C0))) ''
        ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) := by
  ext x
  constructor
  · rintro ⟨⟨⟨t, ht, heqt⟩, ⟨s, hs, heqs⟩⟩, ⟨r, hr, heqr⟩⟩
    refine ⟨((t, s), r), ⟨⟨ht, hs⟩, hr⟩, ?_⟩
    apply (Q0).injective
    rw [(Q0).apply_symm_apply]
    exact Prod.ext (Prod.ext heqt heqs) heqr
  · rintro ⟨z, hz, rfl⟩
    change (Q0) ((Q0).symm _) ∈
      ((AddCircle.closedIntervalArc p u v ×ˢ AddCircle.closedIntervalArc p a b) ×ˢ
        AddCircle.closedIntervalArc p alpha beta)
    rw [(Q0).apply_symm_apply]
    exact ⟨⟨⟨z.1.1, hz.1.1, rfl⟩, ⟨z.1.2, hz.1.2, rfl⟩⟩, ⟨z.2, hz.2, rfl⟩⟩

theorem hamiltonZero_terminal_target_cell_mem_frontier_iff
    {u v a b alpha beta : ℝ} (huv : u ≤ v) (hab : a ≤ b) (halpha : alpha ≤ beta)
    (hthird : v < u + p) (hsecond : b < a + p) (hfirst : beta < alpha + p)
    (x : X0) :
    x ∈ frontier (hamiltonZeroTerminalTargetCell u v a b alpha beta) ↔
      x ∈ hamiltonZeroTerminalTargetCell u v a b alpha beta ∧
        ((Q0 x).1.1 ∈ ({(u : C0), (v : C0)} : Set C0) ∨
         (Q0 x).1.2 ∈ ({(a : C0), (b : C0)} : Set C0) ∨
         (Q0 x).2 ∈ ({(alpha : C0), (beta : C0)} : Set C0)) := by
  have htu := (AddCircle.isCompact_closedIntervalArc p u v).isClosed
  have hsa := (AddCircle.isCompact_closedIntervalArc p a b).isClosed
  have hna := (AddCircle.isCompact_closedIntervalArc p alpha beta).isClosed
  have htf : {(u : C0), (v : C0)} ⊆ AddCircle.closedIntervalArc p u v := by
    rw [← short_arc_frontier huv hthird]
    exact htu.frontier_subset
  have hsf : {(a : C0), (b : C0)} ⊆ AddCircle.closedIntervalArc p a b := by
    rw [← short_arc_frontier hab hsecond]
    exact hsa.frontier_subset
  have hnf : {(alpha : C0), (beta : C0)} ⊆ AddCircle.closedIntervalArc p alpha beta := by
    rw [← short_arc_frontier halpha hfirst]
    exact hna.frontier_subset
  rw [hamiltonZeroTerminalTargetCell, ← (Q0).preimage_frontier]
  simp only [frontier_prod_eq, closure_prod_eq, htu.closure_eq, hsa.closure_eq,
    hna.closure_eq, short_arc_frontier huv hthird, short_arc_frontier hab hsecond,
    short_arc_frontier halpha hfirst, mem_preimage, mem_union, mem_prod]
  aesop

theorem hamiltonZero_terminal_target_cell_projected_frontier
    {u v a b alpha beta : ℝ} (huv : u ≤ v) (hab : a ≤ b) (halpha : alpha ≤ beta)
    (hthird : v < u + p) (hsecond : b < a + p) (hfirst : beta < alpha + p) :
    (fun z : E3 => (Q0).symm (((z.1.1 : C0), (z.1.2 : C0)), (z.2 : C0))) ''
        frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) =
      frontier (hamiltonZeroTerminalTargetCell u v a b alpha beta) := by
  let proj : E3 → X0 := fun z => (Q0).symm (((z.1.1 : C0), (z.1.2 : C0)), (z.2 : C0))
  have hreal (z : E3) : z ∈ frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) ↔
      z ∈ ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) ∧
        (z.1.1 ∈ ({u, v} : Set ℝ) ∨ z.1.2 ∈ ({a, b} : Set ℝ) ∨ z.2 ∈ ({alpha, beta} : Set ℝ)) := by
    simp only [frontier_prod_eq, closure_prod_eq, closure_Icc, frontier_Icc huv,
      frontier_Icc hab, frontier_Icc halpha, mem_union, mem_prod, mem_insert_iff,
      mem_singleton_iff, mem_Icc]
    aesop
  have hcoe {l r z : ℝ} (hw : r < l + p) (hlr : l ≤ r) (hz : z ∈ Icc l r) :
      (z : C0) ∈ ({(l : C0), (r : C0)} : Set C0) ↔ z ∈ ({l, r} : Set ℝ) := by
    simp only [mem_insert_iff, mem_singleton_iff]
    rw [AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show z ∈ Ico l (l + p) from ⟨hz.1, hz.2.trans_lt hw⟩)
      (show l ∈ Ico l (l + p) from ⟨le_rfl, by norm_num⟩),
      AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show z ∈ Ico l (l + p) from ⟨hz.1, hz.2.trans_lt hw⟩)
      (show r ∈ Ico l (l + p) from ⟨hlr, hw⟩)]
  have hmark (z : E3) (hz : z ∈ ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta)) :
      proj z ∈ frontier (hamiltonZeroTerminalTargetCell u v a b alpha beta) ↔
        z ∈ frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) := by
    rw [hamiltonZero_terminal_target_cell_mem_frontier_iff huv hab halpha hthird hsecond hfirst,
      hreal]
    have hm : proj z ∈ hamiltonZeroTerminalTargetCell u v a b alpha beta := by
      rw [hamiltonZero_terminal_target_cell_eq_projected_box]
      exact ⟨z, hz, rfl⟩
    simp only [hm, hz, true_and, proj, (Q0).apply_symm_apply]
    rw [hcoe hthird huv hz.1.1, hcoe hsecond hab hz.1.2, hcoe hfirst halpha hz.2]
  apply Subset.antisymm
  · rintro x ⟨z, hz, rfl⟩
    exact (hmark z (((isClosed_Icc.prod isClosed_Icc).prod isClosed_Icc).frontier_subset hz)).mpr hz
  · intro x hx
    have hm := (hamiltonZero_terminal_target_cell_mem_frontier_iff
      huv hab halpha hthird hsecond hfirst x).mp hx |>.1
    rw [hamiltonZero_terminal_target_cell_eq_projected_box] at hm
    obtain ⟨z, hz, rfl⟩ := hm
    exact ⟨z, (hmark z hz).mp hx, rfl⟩

private theorem complementary_arc_inter {a b : ℝ} (hab : a < b) (hw : b < a + p) :
    AddCircle.closedIntervalArc p a b ∩ AddCircle.closedIntervalArc p b (a + p) =
      {(a : C0), (b : C0)} := by
  ext x
  constructor
  · rintro ⟨⟨s, hs, hsx⟩, ⟨t, ht, htx⟩⟩
    by_cases htop : t = a + p
    · exact Or.inl (htx.symm.trans (htop ▸ AddCircle.coe_add_period p a))
    · have htI : t ∈ Ico a (a + p) := ⟨hab.le.trans ht.1, lt_of_le_of_ne ht.2 htop⟩
      have hsI : s ∈ Ico a (a + p) := ⟨hs.1, hs.2.trans_lt hw⟩
      have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico hsI htI).mp (hsx.trans htx.symm)
      have hsb : s = b := le_antisymm hs.2 (heq ▸ ht.1)
      exact Or.inr (hsx.symm.trans (congrArg (fun r : ℝ => (r : C0)) hsb))
  · rintro (rfl | rfl)
    · exact ⟨⟨a, ⟨le_rfl, hab.le⟩, rfl⟩,
        ⟨a + p, ⟨hw.le, le_rfl⟩, AddCircle.coe_add_period p a⟩⟩
    · exact ⟨⟨b, ⟨hab.le, le_rfl⟩, rfl⟩, ⟨b, ⟨le_rfl, hw.le⟩, rfl⟩⟩

def hamiltonZeroTerminalTargetCells (alpha beta a b : ℝ) (u v : Bool → ℝ)
    (label : Bool × Bool) : Set X0 :=
  hamiltonZeroTerminalTargetCell
    (if label.2 then v label.1 else u label.1)
    (if label.2 then u label.1 + p else v label.1)
    (if label.1 then b else a) (if label.1 then a + p else b) alpha beta

theorem hamiltonZero_terminal_target_cells_inter_frontier
    {alpha beta a b : ℝ} {u v : Bool → ℝ}
    (halpha : alpha < beta) (hfirst : beta < alpha + p)
    (hab : a < b) (hsecond : b < a + p)
    (huv : ∀ s, u s < v s) (hthird : ∀ s, v s < u s + p)
    (i j : Bool × Bool) (hij : i ≠ j) :
    hamiltonZeroTerminalTargetCells alpha beta a b u v i ∩
        hamiltonZeroTerminalTargetCells alpha beta a b u v j ⊆
      frontier (hamiltonZeroTerminalTargetCells alpha beta a b u v i) := by
  intro x hx
  have hbnd {l r : ℝ} (hlr : l < r) (hw : r < l + p) (s : Bool) :
      (if s then l + p else r) < (if s then r else l) + p ∧
      (if s then r else l) ≤ (if s then l + p else r) := by
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> constructor <;> linarith
  apply (hamiltonZero_terminal_target_cell_mem_frontier_iff
    (hbnd (huv i.1) (hthird i.1) i.2).2 (hbnd hab hsecond i.1).2 halpha.le
    (hbnd (huv i.1) (hthird i.1) i.2).1 (hbnd hab hsecond i.1).1 hfirst x).mpr
  refine ⟨hx.1, ?_⟩
  by_cases hs : i.1 = j.1
  · have ht : i.2 ≠ j.2 := fun h => hij (Prod.ext hs h)
    have hm : (Q0 x).1.1 ∈ ({(u i.1 : C0), (v i.1 : C0)} : Set C0) := by
      rw [← complementary_arc_inter (huv i.1) (hthird i.1)]
      have hxi := hx.1.1.1
      have hxj := hx.2.1.1
      change (Q0 x).1.1 ∈ AddCircle.closedIntervalArc p
        (if i.2 then v i.1 else u i.1) (if i.2 then u i.1 + p else v i.1) at hxi
      change (Q0 x).1.1 ∈ AddCircle.closedIntervalArc p
        (if j.2 then v j.1 else u j.1) (if j.2 then u j.1 + p else v j.1) at hxj
      rw [← hs] at hxj
      cases hi : i.2 <;> cases hj : j.2 <;> simp only [hi, hj, ↓reduceIte] at hxi hxj ht
      · exact (ht rfl).elim
      · exact ⟨hxi, hxj⟩
      · exact ⟨hxj, hxi⟩
      · exact (ht rfl).elim
    left
    cases i.2 <;> simpa only [Bool.false_eq_true, ↓reduceIte,
      AddCircle.coe_add_period, Set.pair_comm] using hm
  · have hm : (Q0 x).1.2 ∈ ({(a : C0), (b : C0)} : Set C0) := by
      rw [← complementary_arc_inter hab hsecond]
      have hxi := hx.1.1.2
      have hxj := hx.2.1.2
      change (Q0 x).1.2 ∈ AddCircle.closedIntervalArc p
        (if i.1 then b else a) (if i.1 then a + p else b) at hxi
      change (Q0 x).1.2 ∈ AddCircle.closedIntervalArc p
        (if j.1 then b else a) (if j.1 then a + p else b) at hxj
      cases hi : i.1 <;> cases hj : j.1 <;> simp only [hi, hj, ↓reduceIte] at hxi hxj hs
      · exact (hs True.intro).elim
      · exact ⟨hxi, hxj⟩
      · exact ⟨hxj, hxi⟩
      · exact (hs True.intro).elim
    right; left
    cases i.1 <;> simpa only [Bool.false_eq_true, ↓reduceIte,
      AddCircle.coe_add_period, Set.pair_comm] using hm

theorem hamiltonZero_terminal_target_cells_disjoint_interiors
    {alpha beta a b : ℝ} {u v : Bool → ℝ}
    (halpha : alpha < beta) (hfirst : beta < alpha + p)
    (hab : a < b) (hsecond : b < a + p)
    (huv : ∀ s, u s < v s) (hthird : ∀ s, v s < u s + p) :
    Pairwise (fun i j => Disjoint
      (interior (hamiltonZeroTerminalTargetCells alpha beta a b u v i))
      (interior (hamiltonZeroTerminalTargetCells alpha beta a b u v j))) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hxi hxj
  have hfront := hamiltonZero_terminal_target_cells_inter_frontier
    halpha hfirst hab hsecond huv hthird i j hij ⟨interior_subset hxi, interior_subset hxj⟩
  exact hfront.2 hxi

end PoincareConjecture.M76
