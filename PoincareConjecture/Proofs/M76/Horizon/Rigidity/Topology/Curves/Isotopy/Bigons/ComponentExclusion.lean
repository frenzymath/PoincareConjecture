import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Arcs.InnermostReturningContacts



set_option autoImplicit false
open Set Geometry

namespace Polygon

local notation "V" => (ℝ × ℝ)
local notation "Z" => ((Prod.snd : V → ℝ) ⁻¹' ({0} : Set ℝ))

theorem proper_interval_trapped_of_returning_disk_entry
    {n : ℕ} (P : Polygon V (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    {A B D : Set V} {u v a b : V}
    (hboundary : P.boundary ℝ = A ∪ segment ℝ u v)
    (hB : IsFinitePLBallPair ℝ B {a, b})
    (hBfront : B ∩ frontier D = {a, b})
    (hbase : segment ℝ u v ⊆ frontier D) (hclosedD : closure P.inside ⊆ D)
    (hAB : Disjoint A B) (hentry : (B ∩ P.inside).Nonempty) :
    B \ {a, b} ⊆ P.inside ∧ B ⊆ closure P.inside ∧
      a ∈ segment ℝ u v ∧ b ∈ segment ℝ u v := by
  have hinsideD : P.inside ⊆ interior D :=
    interior_maximal (subset_closure.trans hclosedD) (P.isOpen_inside hP hi)
  have havoid : Disjoint (frontier P.inside) (B \ {a, b}) := by
    rw [P.frontier_inside hP hi]
    apply disjoint_left.mpr
    intro x hxP hxB
    rcases hboundary ▸ hxP with hxA | hxseg
    · exact disjoint_left.mp hAB hxA hxB.1
    · exact hxB.2 (hBfront.subset ⟨hxB.1, hbase hxseg⟩)
  obtain ⟨x, hxB, hxP⟩ := hentry
  have hxends : x ∉ ({a, b} : Set V) := fun he =>
    disjoint_left.mp disjoint_interior_frontier (hinsideD hxP)
      (hBfront.symm.subset he).2
  have hinside : B \ {a, b} ⊆ P.inside :=
    hB.isConnected_sdiff.isPreconnected.m76_subset_of_disjoint_frontier
      (P.isOpen_inside hP hi) havoid ⟨x, ⟨hxB, hxends⟩, hxP⟩
  have hBcl : B ⊆ closure P.inside := by
    rw [← hB.closure_sdiff]
    exact closure_mono hinside
  have hends (y : V) (hy : y ∈ ({a, b} : Set V)) : y ∈ segment ℝ u v := by
    have hyB := hB.1 hy
    have hyF := (hBfront.symm.subset hy).2
    have hycl := hBcl hyB
    have hynot : y ∉ P.inside := fun h =>
      disjoint_left.mp disjoint_interior_frontier (hinsideD h) hyF
    rw [closure_eq_self_union_frontier, P.frontier_inside hP hi] at hycl
    rcases hboundary ▸ hycl.resolve_left hynot with hyA | hyseg
    · exact (disjoint_left.mp hAB hyA hyB).elim
    · exact hyseg
  exact ⟨hinside, hBcl, hends a (by simp), hends b (by simp)⟩

theorem closed_returning_disk_disjoint_of_nonreturning_component
    {n : ℕ} (P : Polygon V (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    (hup : ∀ i, 0 ≤ (P i).2) {A B D : Set V} {u v a b : V}
    (hboundary : P.boundary ℝ = A ∪ segment ℝ u v)
    (hA : IsFinitePLBallPair ℝ A {u, v}) (hAz : A ∩ Z = {u, v})
    (huv : u.1 < v.1) (hB : IsFinitePLBallPair ℝ B {a, b})
    (hBfront : B ∩ frontier D = {a, b}) (hBD : B ⊆ D)
    (hDupper : ∀ z ∈ D, 0 ≤ z.2) (hDaxis : D ∩ Z ⊆ frontier D)
    (hclosedD : closure P.inside ⊆ D) (hAB : Disjoint A B)
    (hnonreturn : ¬ (a ∈ Z ∧ b ∈ Z)) : Disjoint (closure P.inside) B := by
  have hu : u ∈ A ∩ Z := hAz.symm.subset (by simp)
  have hv : v ∈ A ∩ Z := hAz.symm.subset (by simp)
  have hbase : segment ℝ u v ⊆ frontier D := by
    intro x hx
    have hxP : x ∈ P.boundary ℝ := hboundary.symm.subset (Or.inr hx)
    have hxcl : x ∈ closure P.inside :=
      frontier_subset_closure ((P.frontier_inside hP hi).symm ▸ hxP)
    exact hDaxis ⟨hclosedD hxcl, segment_subset_returning_axis hu.2 hv.2 hx⟩
  apply disjoint_left.mpr
  intro q hqcl hqB
  rw [closure_eq_self_union_frontier, P.frontier_inside hP hi] at hqcl
  rcases hqcl with hqI | hqP
  · obtain ⟨_, _, ha, hb⟩ := P.proper_interval_trapped_of_returning_disk_entry
      hP hi hboundary hB hBfront hbase hclosedD hAB ⟨q, hqB, hqI⟩
    exact hnonreturn ⟨segment_subset_returning_axis hu.2 hv.2 ha,
      segment_subset_returning_axis hu.2 hv.2 hb⟩
  · rcases hboundary ▸ hqP with hqA | hqseg
    · exact disjoint_left.mp hAB hqA hqB
    · have hq0 : q.2 = 0 := segment_subset_returning_axis hu.2 hv.2 hqseg
      have hqneq0 : q ≠ u := fun h => disjoint_left.mp hAB (h.symm ▸ hu.1) hqB
      have hqneq1 : q ≠ v := fun h => disjoint_left.mp hAB (h.symm ▸ hv.1) hqB
      have hqIcc : q.1 ∈ Icc u.1 v.1 := by
        rw [returning_axis_segment hu.2 hv.2 huv.le] at hqseg
        exact hqseg.1
      have hqstrict : q.1 ∈ Ioo u.1 v.1 := by
        refine ⟨lt_of_le_of_ne hqIcc.1 ?_, lt_of_le_of_ne hqIcc.2 ?_⟩
        · exact fun h => hqneq0 (Prod.ext h.symm (hq0.trans hu.2.symm))
        · exact fun h => hqneq1 (Prod.ext h (hq0.trans hv.2.symm))
      obtain ⟨_, _, ha, hb⟩ := P.interval_trapped_of_returning_base_contact
        hP hi hup hboundary hA hAz hB hBfront hBD hDupper hDaxis hclosedD
        hAB hqB hq0 hqstrict
      exact hnonreturn ⟨segment_subset_returning_axis hu.2 hv.2 ha,
        segment_subset_returning_axis hu.2 hv.2 hb⟩

end Polygon
