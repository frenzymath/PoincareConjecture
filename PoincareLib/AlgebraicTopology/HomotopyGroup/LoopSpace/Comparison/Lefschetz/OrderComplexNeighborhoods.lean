import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.OrderComplexRestriction

/-!
# Open covers for minimal-vertex induction

For a minimal selected vertex, its deletion and upper cone define an open
cover of the selected coordinate neighborhood. Their intersection is the
strict upper-link neighborhood. The identities take place in one fixed
geometric realization, so inverse images under a covering give the exact
open sets required by singular Mayer-Vietoris.
Source: Hatcher, Theorem 2.27, printed pp. 128-130.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace PoincareMT.Proofs.M59

open M02.Topology

variable {J : Type u} [PartialOrder J] [Fintype J]

/-- Positive selected total weight is equivalent to a positive selected
coordinate. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem mem_orderComplexNeighborhood_iff (s : Finset J)
    (z : (finiteOrderComplex J).space) :
    z ∈ orderComplexNeighborhood s ↔ ∃ i ∈ s, 0 < z.val i := by
  exact Finset.sum_pos_iff_of_nonneg
    (fun i _ => ((finiteOrderComplex_space J z.val).mp z.property).1 i)

/-- Vertex-set inclusion gives inclusion of the actual open coordinate
neighborhoods. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem orderComplexNeighborhood_mono {s t : Finset J} (h : s ⊆ t) :
    orderComplexNeighborhood s ⊆ orderComplexNeighborhood t := by
  intro z hz
  obtain ⟨i, hi, hpos⟩ := (mem_orderComplexNeighborhood_iff s z).mp hz
  exact (mem_orderComplexNeighborhood_iff t z).mpr ⟨i, h hi, hpos⟩

open scoped Classical in
/-- Vertex-set unions give literal open-neighborhood unions.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem orderComplexNeighborhood_union (s t : Finset J) :
    orderComplexNeighborhood (s ∪ t) =
      orderComplexNeighborhood s ∪ orderComplexNeighborhood t := by
  ext z
  simp only [mem_orderComplexNeighborhood_iff, Finset.mem_union, Set.mem_union,
    or_and_right, exists_or]

/-- The full selected vertex set gives the entire realization.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem orderComplexNeighborhood_univ :
    orderComplexNeighborhood (Finset.univ : Finset J) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  change 0 < ∑ i : J, z.val i
  rw [((finiteOrderComplex_space J z.val).mp z.property).2.1]
  exact zero_lt_one

open scoped Classical in
/-- A selected vertex's deletion and upper cone cover the original
selected neighborhood. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem orderComplexNeighborhood_minimal_union (s : Finset J) (v : J) :
    orderComplexNeighborhood (s.erase v) ∪
        orderComplexNeighborhood (s.filter (v ≤ ·)) = orderComplexNeighborhood s := by
  rw [← orderComplexNeighborhood_union]
  congr 1
  ext j
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_filter]
  constructor
  · rintro (⟨_, hj⟩ | ⟨hj, _⟩) <;> exact hj
  · intro hj
    by_cases h : j = v
    · exact Or.inr ⟨hj, h.ge⟩
    · exact Or.inl ⟨h, hj⟩

open scoped Classical in
/-- The overlap is precisely the strict upper-link neighborhood; the
proof retains the actual chain support of each point.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem orderComplexNeighborhood_minimal_inter (s : Finset J) (v : J)
    (hminimal : ∀ j ∈ s, j ≤ v → j = v) :
    orderComplexNeighborhood (s.erase v) ∩
        orderComplexNeighborhood (s.filter (v ≤ ·)) =
      orderComplexNeighborhood (s.filter (v < ·)) := by
  ext z
  constructor
  · rintro ⟨ha, hb⟩
    obtain ⟨i, hi, hzi⟩ := (mem_orderComplexNeighborhood_iff _ z).mp ha
    obtain ⟨j, hj, hzj⟩ := (mem_orderComplexNeighborhood_iff _ z).mp hb
    obtain ⟨his, hiv⟩ := Finset.mem_filter.mp hj
    by_cases hvj : v = j
    · subst j
      have hc := ((finiteOrderComplex_space J z.val).mp z.property).2.2 i v
        (ne_of_gt hzi) (ne_of_gt hzj)
      have hne := (Finset.mem_erase.mp hi).1
      have hsi := (Finset.mem_erase.mp hi).2
      rcases hc with hiv | hvi
      · exact (hne (hminimal i hsi hiv)).elim
      · exact (mem_orderComplexNeighborhood_iff _ z).mpr
          ⟨i, Finset.mem_filter.mpr ⟨hsi, lt_of_le_of_ne hvi hne.symm⟩, hzi⟩
    · exact (mem_orderComplexNeighborhood_iff _ z).mpr
        ⟨j, Finset.mem_filter.mpr ⟨his, lt_of_le_of_ne hiv hvj⟩, hzj⟩
  · intro hz
    obtain ⟨j, hj, hzj⟩ := (mem_orderComplexNeighborhood_iff _ z).mp hz
    obtain ⟨hsj, hvj⟩ := Finset.mem_filter.mp hj
    exact ⟨(mem_orderComplexNeighborhood_iff _ z).mpr
      ⟨j, Finset.mem_erase.mpr ⟨ne_of_gt hvj, hsj⟩, hzj⟩,
      (mem_orderComplexNeighborhood_iff _ z).mpr
      ⟨j, Finset.mem_filter.mpr ⟨hsj, hvj.le⟩, hzj⟩⟩

end PoincareMT.Proofs.M59
