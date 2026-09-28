import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.Sectors.Coordinates

set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface
namespace ChartCircleArrangementVertexPatch

private theorem sectorInterval_disjoint_closed {c w : ℝ} {i j : Bool} (hij : i ≠ j) :
    Disjoint (sectorInterval c w i) (closedSectorInterval c w j) := by
  apply disjoint_left.mpr
  intro x hx hy
  cases i <;> cases j <;> simp_all [sectorInterval, closedSectorInterval] <;> linarith

private theorem eq_zero_of_opposite_interval {c w s : ℝ} {i j : Bool}
    (hij : i ≠ j) (hs : 0 ≤ s)
    (hmem : (if i then s else -s) + c ∈ closedSectorInterval c w j) : s = 0 := by
  cases i <;> cases j <;> simp_all [closedSectorInterval] <;> linarith

universe u
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  {r : M → ℝ} {p : M}
variable (P : ChartCircleArrangementVertexPatch r p)

theorem sector_disjoint_closedSector {i j : Bool × Bool} (hij : i ≠ j) :
    Disjoint (P.sector i) (P.closedSector j) := by
  apply disjoint_left.mpr
  rintro _ ⟨q, hq, rfl⟩ ⟨v, hv, heq⟩
  have he := P.productCoordinates.injOn (P.closedSectorBox_subset_source j hv)
    (P.closedSectorBox_subset_source i (P.sectorBox_subset_closed i hq)) heq
  subst v
  have hne : i.1 ≠ j.1 ∨ i.2 ≠ j.2 := by
    by_contra! h
    exact hij (Prod.ext h.1 h.2)
  rcases hne with hne | hne
  · exact disjoint_left.mp (sectorInterval_disjoint_closed hne) hq.1 hv.1
  · exact disjoint_left.mp (sectorInterval_disjoint_closed hne) hq.2 hv.2

def firstSide (i : Bool × Bool) (ε : ℝ) : Set M :=
  (fun t => P.sectorCoordinates i (t, 0)) '' Icc (0 : ℝ) ε

def secondSide (i : Bool × Bool) (ε : ℝ) : Set M :=
  (fun t => P.sectorCoordinates i (0, t)) '' Icc (0 : ℝ) ε

theorem mem_firstSide (i : Bool × Bool) {ε : ℝ} (hε : 0 ≤ ε) : p ∈ P.firstSide i ε :=
  ⟨0, ⟨le_rfl, hε⟩, P.sectorCoordinates_zero i⟩

theorem mem_secondSide (i : Bool × Bool) {ε : ℝ} (hε : 0 ≤ ε) : p ∈ P.secondSide i ε :=
  ⟨0, ⟨le_rfl, hε⟩, P.sectorCoordinates_zero i⟩

theorem firstSide_eq_of_fst_eq {i j : Bool × Bool} (hij : i.1 = j.1) (ε : ℝ) :
    P.firstSide i ε = P.firstSide j ε := by
  unfold firstSide
  congr 1
  funext t
  change P.productCoordinates (sectorParameterEquiv P.center i (t, 0)) =
    P.productCoordinates (sectorParameterEquiv P.center j (t, 0))
  simp only [sectorParameterEquiv_apply, hij, neg_zero, ite_self]

theorem secondSide_eq_of_snd_eq {i j : Bool × Bool} (hij : i.2 = j.2) (ε : ℝ) :
    P.secondSide i ε = P.secondSide j ε := by
  unfold secondSide
  congr 1
  funext t
  change P.productCoordinates (sectorParameterEquiv P.center i (0, t)) =
    P.productCoordinates (sectorParameterEquiv P.center j (0, t))
  simp only [sectorParameterEquiv_apply, hij, neg_zero, ite_self]

theorem firstSide_inter_opposite_sector {i j : Bool × Bool} {ε : ℝ}
    (hij : i.1 ≠ j.1) (hε : ε ≤ P.width) :
    P.firstSide i ε ∩ P.closedSector j ⊆ {p} := by
  rintro _ ⟨⟨s, hs, rfl⟩, v, hv, heq⟩
  have hq : (s, (0 : ℝ)) ∈ Icc (0 : ℝ) P.width ×ˢ Icc (0 : ℝ) P.width :=
    ⟨⟨hs.1, hs.2.trans hε⟩, le_rfl, P.width_pos.le⟩
  have hsource := (P.sectorCoordinates_square_source i hq).2
  have hvq := P.productCoordinates.injOn (P.closedSectorBox_subset_source j hv) hsource heq
  change v = sectorParameterEquiv P.center i (s, 0) at hvq
  rw [hvq] at hv
  have hs0 : s = 0 := eq_zero_of_opposite_interval hij hs.1
    (by simpa only [sectorParameterEquiv_apply] using hv.1)
  rw [hs0]
  exact P.sectorCoordinates_zero i

theorem secondSide_inter_opposite_sector {i j : Bool × Bool} {ε : ℝ}
    (hij : i.2 ≠ j.2) (hε : ε ≤ P.width) :
    P.secondSide i ε ∩ P.closedSector j ⊆ {p} := by
  rintro _ ⟨⟨s, hs, rfl⟩, v, hv, heq⟩
  have hq : ((0 : ℝ), s) ∈ Icc (0 : ℝ) P.width ×ˢ Icc (0 : ℝ) P.width :=
    ⟨⟨le_rfl, P.width_pos.le⟩, hs.1, hs.2.trans hε⟩
  have hsource := (P.sectorCoordinates_square_source i hq).2
  have hvq := P.productCoordinates.injOn (P.closedSectorBox_subset_source j hv) hsource heq
  change v = sectorParameterEquiv P.center i (0, s) at hvq
  rw [hvq] at hv
  have hs0 : s = 0 := eq_zero_of_opposite_interval hij hs.1
    (by simpa only [sectorParameterEquiv_apply] using hv.2)
  rw [hs0]
  exact P.sectorCoordinates_zero i

theorem cap_intersections {ε : ℝ} (hε : 0 ≤ ε) (hwidth : ε ≤ P.width)
    (S : Bool × Bool → Set M)
    (hclosed : ∀ i, S i ⊆ P.closedSector i)
    (hboundary : ∀ i, S i ⊆ P.sector i ∪ (P.firstSide i ε ∪ P.secondSide i ε))
    (hfirst : ∀ i, P.firstSide i ε ⊆ S i)
    (hsecond : ∀ i, P.secondSide i ε ⊆ S i)
    {i j : Bool × Bool} (hij : i ≠ j) :
    (i.1 = j.1 → S i ∩ S j = P.firstSide i ε) ∧
    (i.2 = j.2 → S i ∩ S j = P.secondSide i ε) ∧
    (i.1 ≠ j.1 → i.2 ≠ j.2 → S i ∩ S j = {p}) := by
  have haxis {z : M} (hz : z ∈ S i ∩ S j) :
      z ∈ P.firstSide i ε ∪ P.secondSide i ε := by
    rcases hboundary i hz.1 with h | h
    · exact (disjoint_left.mp (P.sector_disjoint_closedSector hij) h (hclosed j hz.2)).elim
    · exact h
  have hp (k : Bool × Bool) : p ∈ S k := hfirst k (P.mem_firstSide k hε)
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    have hne : i.2 ≠ j.2 := fun h => hij (Prod.ext heq h)
    apply Subset.antisymm
    · intro z hz
      rcases haxis hz with h | h
      · exact h
      · have hz0 := P.secondSide_inter_opposite_sector hne hwidth ⟨h, hclosed j hz.2⟩
        exact mem_singleton_iff.mp hz0 ▸ P.mem_firstSide i hε
    · intro z hz
      exact ⟨hfirst i hz, hfirst j ((P.firstSide_eq_of_fst_eq heq ε) ▸ hz)⟩
  · intro heq
    have hne : i.1 ≠ j.1 := fun h => hij (Prod.ext h heq)
    apply Subset.antisymm
    · intro z hz
      rcases haxis hz with h | h
      · have hz0 := P.firstSide_inter_opposite_sector hne hwidth ⟨h, hclosed j hz.2⟩
        exact mem_singleton_iff.mp hz0 ▸ P.mem_secondSide i hε
      · exact h
    · intro z hz
      exact ⟨hsecond i hz, hsecond j ((P.secondSide_eq_of_snd_eq heq ε) ▸ hz)⟩
  · intro hne₁ hne₂
    apply Subset.antisymm
    · intro z hz
      rcases haxis hz with h | h
      · exact P.firstSide_inter_opposite_sector hne₁ hwidth ⟨h, hclosed j hz.2⟩
      · exact P.secondSide_inter_opposite_sector hne₂ hwidth ⟨h, hclosed j hz.2⟩
    · rintro z rfl
      exact ⟨hp i, hp j⟩

theorem exists_neighborhood_subset_sector_caps (S : Bool × Bool → Set M)
    (hnear : ∀ i, ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ∩ P.closedSector i ⊆ S i) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ ⋃ i, S i := by
  choose V hV hpV hsub using hnear
  refine ⟨P.openCarrier ∩ ⋂ i, V i,
    P.isOpen_openCarrier.inter (isOpen_iInter_of_finite hV),
    ⟨P.mem_openCarrier, mem_iInter.mpr hpV⟩, ?_⟩
  intro z hz
  have hzP := P.openCarrier_subset_carrier hz.1
  rw [← P.closedSectors_cover] at hzP
  obtain ⟨i, hi⟩ := mem_iUnion.mp hzP
  exact mem_iUnion.mpr ⟨i, hsub i ⟨mem_iInter.mp hz.2 i, hi⟩⟩

end ChartCircleArrangementVertexPatch
end PoincareConjecture.Topology.Surface
